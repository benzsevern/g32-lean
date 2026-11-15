import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_090 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 90 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_090_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 13 14, g32p_row02_traceSegment_090_0000_0013, g32p_row02_traceSegment_090_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 27 13 14, g32p_row02_traceSegment_090_0027_0013, g32p_row02_traceSegment_090_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 27 27, g32p_row02_traceSegment_090_0000_0027, g32p_row02_traceSegment_090_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 54 13 14, g32p_row02_traceSegment_090_0054_0013, g32p_row02_traceSegment_090_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 81 13 14, g32p_row02_traceSegment_090_0081_0013, g32p_row02_traceSegment_090_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 54 27 27, g32p_row02_traceSegment_090_0054_0027, g32p_row02_traceSegment_090_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 54 54, g32p_row02_traceSegment_090_0000_0054, g32p_row02_traceSegment_090_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 108 13 14, g32p_row02_traceSegment_090_0108_0013, g32p_row02_traceSegment_090_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 135 13 14, g32p_row02_traceSegment_090_0135_0013, g32p_row02_traceSegment_090_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 108 27 27, g32p_row02_traceSegment_090_0108_0027, g32p_row02_traceSegment_090_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 162 13 14, g32p_row02_traceSegment_090_0162_0013, g32p_row02_traceSegment_090_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 189 13 14, g32p_row02_traceSegment_090_0189_0013, g32p_row02_traceSegment_090_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 162 27 27, g32p_row02_traceSegment_090_0162_0027, g32p_row02_traceSegment_090_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 108 54 54, g32p_row02_traceSegment_090_0108_0054, g32p_row02_traceSegment_090_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 108 108, g32p_row02_traceSegment_090_0000_0108, g32p_row02_traceSegment_090_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 216 13 14, g32p_row02_traceSegment_090_0216_0013, g32p_row02_traceSegment_090_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 243 13 14, g32p_row02_traceSegment_090_0243_0013, g32p_row02_traceSegment_090_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 216 27 27, g32p_row02_traceSegment_090_0216_0027, g32p_row02_traceSegment_090_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 270 13 14, g32p_row02_traceSegment_090_0270_0013, g32p_row02_traceSegment_090_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 297 13 14, g32p_row02_traceSegment_090_0297_0013, g32p_row02_traceSegment_090_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 270 27 27, g32p_row02_traceSegment_090_0270_0027, g32p_row02_traceSegment_090_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 216 54 54, g32p_row02_traceSegment_090_0216_0054, g32p_row02_traceSegment_090_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 324 13 14, g32p_row02_traceSegment_090_0324_0013, g32p_row02_traceSegment_090_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 351 13 14, g32p_row02_traceSegment_090_0351_0013, g32p_row02_traceSegment_090_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 324 27 27, g32p_row02_traceSegment_090_0324_0027, g32p_row02_traceSegment_090_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 378 13 14, g32p_row02_traceSegment_090_0378_0013, g32p_row02_traceSegment_090_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 405 13 14, g32p_row02_traceSegment_090_0405_0013, g32p_row02_traceSegment_090_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 378 27 27, g32p_row02_traceSegment_090_0378_0027, g32p_row02_traceSegment_090_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 324 54 54, g32p_row02_traceSegment_090_0324_0054, g32p_row02_traceSegment_090_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 216 108 108, g32p_row02_traceSegment_090_0216_0108, g32p_row02_traceSegment_090_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 216 216, g32p_row02_traceSegment_090_0000_0216, g32p_row02_traceSegment_090_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 432 13 14, g32p_row02_traceSegment_090_0432_0013, g32p_row02_traceSegment_090_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 459 13 14, g32p_row02_traceSegment_090_0459_0013, g32p_row02_traceSegment_090_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 432 27 27, g32p_row02_traceSegment_090_0432_0027, g32p_row02_traceSegment_090_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 486 13 14, g32p_row02_traceSegment_090_0486_0013, g32p_row02_traceSegment_090_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 513 13 14, g32p_row02_traceSegment_090_0513_0013, g32p_row02_traceSegment_090_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 486 27 27, g32p_row02_traceSegment_090_0486_0027, g32p_row02_traceSegment_090_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 432 54 54, g32p_row02_traceSegment_090_0432_0054, g32p_row02_traceSegment_090_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 540 13 14, g32p_row02_traceSegment_090_0540_0013, g32p_row02_traceSegment_090_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 567 13 14, g32p_row02_traceSegment_090_0567_0013, g32p_row02_traceSegment_090_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 540 27 27, g32p_row02_traceSegment_090_0540_0027, g32p_row02_traceSegment_090_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 594 13 14, g32p_row02_traceSegment_090_0594_0013, g32p_row02_traceSegment_090_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 621 13 14, g32p_row02_traceSegment_090_0621_0013, g32p_row02_traceSegment_090_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 594 27 27, g32p_row02_traceSegment_090_0594_0027, g32p_row02_traceSegment_090_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 540 54 54, g32p_row02_traceSegment_090_0540_0054, g32p_row02_traceSegment_090_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 432 108 108, g32p_row02_traceSegment_090_0432_0108, g32p_row02_traceSegment_090_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 648 13 14, g32p_row02_traceSegment_090_0648_0013, g32p_row02_traceSegment_090_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 675 13 14, g32p_row02_traceSegment_090_0675_0013, g32p_row02_traceSegment_090_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 648 27 27, g32p_row02_traceSegment_090_0648_0027, g32p_row02_traceSegment_090_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 702 13 14, g32p_row02_traceSegment_090_0702_0013, g32p_row02_traceSegment_090_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 729 13 14, g32p_row02_traceSegment_090_0729_0013, g32p_row02_traceSegment_090_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 702 27 27, g32p_row02_traceSegment_090_0702_0027, g32p_row02_traceSegment_090_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 648 54 54, g32p_row02_traceSegment_090_0648_0054, g32p_row02_traceSegment_090_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 756 13 14, g32p_row02_traceSegment_090_0756_0013, g32p_row02_traceSegment_090_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 783 13 14, g32p_row02_traceSegment_090_0783_0013, g32p_row02_traceSegment_090_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 756 27 27, g32p_row02_traceSegment_090_0756_0027, g32p_row02_traceSegment_090_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 810 13 14, g32p_row02_traceSegment_090_0810_0013, g32p_row02_traceSegment_090_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 837 13 14, g32p_row02_traceSegment_090_0837_0013, g32p_row02_traceSegment_090_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 810 27 27, g32p_row02_traceSegment_090_0810_0027, g32p_row02_traceSegment_090_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 756 54 54, g32p_row02_traceSegment_090_0756_0054, g32p_row02_traceSegment_090_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 648 108 108, g32p_row02_traceSegment_090_0648_0108, g32p_row02_traceSegment_090_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 432 216 216, g32p_row02_traceSegment_090_0432_0216, g32p_row02_traceSegment_090_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_090 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 432 432, g32p_row02_traceSegment_090_0000_0432, g32p_row02_traceSegment_090_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 864 13 14, g32p_row02_traceSegment_090_0864_0013, g32p_row02_traceSegment_090_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 891 13 14, g32p_row02_traceSegment_090_0891_0013, g32p_row02_traceSegment_090_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 864 27 27, g32p_row02_traceSegment_090_0864_0027, g32p_row02_traceSegment_090_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 918 13 14, g32p_row02_traceSegment_090_0918_0013, g32p_row02_traceSegment_090_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 945 13 14, g32p_row02_traceSegment_090_0945_0013, g32p_row02_traceSegment_090_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 918 27 27, g32p_row02_traceSegment_090_0918_0027, g32p_row02_traceSegment_090_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 864 54 54, g32p_row02_traceSegment_090_0864_0054, g32p_row02_traceSegment_090_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 972 13 14, g32p_row02_traceSegment_090_0972_0013, g32p_row02_traceSegment_090_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 999 13 14, g32p_row02_traceSegment_090_0999_0013, g32p_row02_traceSegment_090_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 972 27 27, g32p_row02_traceSegment_090_0972_0027, g32p_row02_traceSegment_090_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1026 13 14, g32p_row02_traceSegment_090_1026_0013, g32p_row02_traceSegment_090_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1053 13 14, g32p_row02_traceSegment_090_1053_0013, g32p_row02_traceSegment_090_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1026 27 27, g32p_row02_traceSegment_090_1026_0027, g32p_row02_traceSegment_090_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 972 54 54, g32p_row02_traceSegment_090_0972_0054, g32p_row02_traceSegment_090_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 864 108 108, g32p_row02_traceSegment_090_0864_0108, g32p_row02_traceSegment_090_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1080 13 14, g32p_row02_traceSegment_090_1080_0013, g32p_row02_traceSegment_090_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1107 13 14, g32p_row02_traceSegment_090_1107_0013, g32p_row02_traceSegment_090_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1080 27 27, g32p_row02_traceSegment_090_1080_0027, g32p_row02_traceSegment_090_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1134 13 14, g32p_row02_traceSegment_090_1134_0013, g32p_row02_traceSegment_090_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1161 13 14, g32p_row02_traceSegment_090_1161_0013, g32p_row02_traceSegment_090_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1134 27 27, g32p_row02_traceSegment_090_1134_0027, g32p_row02_traceSegment_090_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1080 54 54, g32p_row02_traceSegment_090_1080_0054, g32p_row02_traceSegment_090_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1188 13 14, g32p_row02_traceSegment_090_1188_0013, g32p_row02_traceSegment_090_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1215 13 14, g32p_row02_traceSegment_090_1215_0013, g32p_row02_traceSegment_090_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1188 27 27, g32p_row02_traceSegment_090_1188_0027, g32p_row02_traceSegment_090_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1242 13 14, g32p_row02_traceSegment_090_1242_0013, g32p_row02_traceSegment_090_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1269 13 14, g32p_row02_traceSegment_090_1269_0013, g32p_row02_traceSegment_090_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1242 27 27, g32p_row02_traceSegment_090_1242_0027, g32p_row02_traceSegment_090_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1188 54 54, g32p_row02_traceSegment_090_1188_0054, g32p_row02_traceSegment_090_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1080 108 108, g32p_row02_traceSegment_090_1080_0108, g32p_row02_traceSegment_090_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 864 216 216, g32p_row02_traceSegment_090_0864_0216, g32p_row02_traceSegment_090_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1296 13 14, g32p_row02_traceSegment_090_1296_0013, g32p_row02_traceSegment_090_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1323 13 14, g32p_row02_traceSegment_090_1323_0013, g32p_row02_traceSegment_090_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1296 27 27, g32p_row02_traceSegment_090_1296_0027, g32p_row02_traceSegment_090_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1350 13 14, g32p_row02_traceSegment_090_1350_0013, g32p_row02_traceSegment_090_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1377 13 14, g32p_row02_traceSegment_090_1377_0013, g32p_row02_traceSegment_090_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1350 27 27, g32p_row02_traceSegment_090_1350_0027, g32p_row02_traceSegment_090_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1296 54 54, g32p_row02_traceSegment_090_1296_0054, g32p_row02_traceSegment_090_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1404 13 14, g32p_row02_traceSegment_090_1404_0013, g32p_row02_traceSegment_090_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1431 13 14, g32p_row02_traceSegment_090_1431_0013, g32p_row02_traceSegment_090_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1404 27 27, g32p_row02_traceSegment_090_1404_0027, g32p_row02_traceSegment_090_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1458 13 14, g32p_row02_traceSegment_090_1458_0013, g32p_row02_traceSegment_090_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1485 13 14, g32p_row02_traceSegment_090_1485_0013, g32p_row02_traceSegment_090_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1458 27 27, g32p_row02_traceSegment_090_1458_0027, g32p_row02_traceSegment_090_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1404 54 54, g32p_row02_traceSegment_090_1404_0054, g32p_row02_traceSegment_090_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1296 108 108, g32p_row02_traceSegment_090_1296_0108, g32p_row02_traceSegment_090_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1512 13 14, g32p_row02_traceSegment_090_1512_0013, g32p_row02_traceSegment_090_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1539 13 14, g32p_row02_traceSegment_090_1539_0013, g32p_row02_traceSegment_090_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1512 27 27, g32p_row02_traceSegment_090_1512_0027, g32p_row02_traceSegment_090_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1566 13 14, g32p_row02_traceSegment_090_1566_0013, g32p_row02_traceSegment_090_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1593 13 14, g32p_row02_traceSegment_090_1593_0013, g32p_row02_traceSegment_090_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1566 27 27, g32p_row02_traceSegment_090_1566_0027, g32p_row02_traceSegment_090_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1512 54 54, g32p_row02_traceSegment_090_1512_0054, g32p_row02_traceSegment_090_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1620 13 14, g32p_row02_traceSegment_090_1620_0013, g32p_row02_traceSegment_090_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1647 13 14, g32p_row02_traceSegment_090_1647_0013, g32p_row02_traceSegment_090_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1620 27 27, g32p_row02_traceSegment_090_1620_0027, g32p_row02_traceSegment_090_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1674 13 14, g32p_row02_traceSegment_090_1674_0013, g32p_row02_traceSegment_090_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1701 13 14, g32p_row02_traceSegment_090_1701_0013, g32p_row02_traceSegment_090_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1674 27 27, g32p_row02_traceSegment_090_1674_0027, g32p_row02_traceSegment_090_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1620 54 54, g32p_row02_traceSegment_090_1620_0054, g32p_row02_traceSegment_090_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1512 108 108, g32p_row02_traceSegment_090_1512_0108, g32p_row02_traceSegment_090_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1296 216 216, g32p_row02_traceSegment_090_1296_0216, g32p_row02_traceSegment_090_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_090 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 864 432 432, g32p_row02_traceSegment_090_0864_0432, g32p_row02_traceSegment_090_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_090 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 864 864, g32p_row02_traceSegment_090_0000_0864, g32p_row02_traceSegment_090_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1728 13 14, g32p_row02_traceSegment_090_1728_0013, g32p_row02_traceSegment_090_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1755 13 14, g32p_row02_traceSegment_090_1755_0013, g32p_row02_traceSegment_090_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1728 27 27, g32p_row02_traceSegment_090_1728_0027, g32p_row02_traceSegment_090_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1782 13 14, g32p_row02_traceSegment_090_1782_0013, g32p_row02_traceSegment_090_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1809 13 14, g32p_row02_traceSegment_090_1809_0013, g32p_row02_traceSegment_090_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1782 27 27, g32p_row02_traceSegment_090_1782_0027, g32p_row02_traceSegment_090_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1728 54 54, g32p_row02_traceSegment_090_1728_0054, g32p_row02_traceSegment_090_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1836 13 14, g32p_row02_traceSegment_090_1836_0013, g32p_row02_traceSegment_090_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1863 13 14, g32p_row02_traceSegment_090_1863_0013, g32p_row02_traceSegment_090_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1836 27 27, g32p_row02_traceSegment_090_1836_0027, g32p_row02_traceSegment_090_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1890 13 14, g32p_row02_traceSegment_090_1890_0013, g32p_row02_traceSegment_090_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1917 13 14, g32p_row02_traceSegment_090_1917_0013, g32p_row02_traceSegment_090_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1890 27 27, g32p_row02_traceSegment_090_1890_0027, g32p_row02_traceSegment_090_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1836 54 54, g32p_row02_traceSegment_090_1836_0054, g32p_row02_traceSegment_090_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1728 108 108, g32p_row02_traceSegment_090_1728_0108, g32p_row02_traceSegment_090_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1944 13 14, g32p_row02_traceSegment_090_1944_0013, g32p_row02_traceSegment_090_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1971 13 14, g32p_row02_traceSegment_090_1971_0013, g32p_row02_traceSegment_090_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1944 27 27, g32p_row02_traceSegment_090_1944_0027, g32p_row02_traceSegment_090_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1998 13 14, g32p_row02_traceSegment_090_1998_0013, g32p_row02_traceSegment_090_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2025 13 14, g32p_row02_traceSegment_090_2025_0013, g32p_row02_traceSegment_090_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1998 27 27, g32p_row02_traceSegment_090_1998_0027, g32p_row02_traceSegment_090_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1944 54 54, g32p_row02_traceSegment_090_1944_0054, g32p_row02_traceSegment_090_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2052 13 14, g32p_row02_traceSegment_090_2052_0013, g32p_row02_traceSegment_090_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2079 13 14, g32p_row02_traceSegment_090_2079_0013, g32p_row02_traceSegment_090_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2052 27 27, g32p_row02_traceSegment_090_2052_0027, g32p_row02_traceSegment_090_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2106 13 14, g32p_row02_traceSegment_090_2106_0013, g32p_row02_traceSegment_090_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2133 13 14, g32p_row02_traceSegment_090_2133_0013, g32p_row02_traceSegment_090_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2106 27 27, g32p_row02_traceSegment_090_2106_0027, g32p_row02_traceSegment_090_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2052 54 54, g32p_row02_traceSegment_090_2052_0054, g32p_row02_traceSegment_090_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1944 108 108, g32p_row02_traceSegment_090_1944_0108, g32p_row02_traceSegment_090_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1728 216 216, g32p_row02_traceSegment_090_1728_0216, g32p_row02_traceSegment_090_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2160 13 14, g32p_row02_traceSegment_090_2160_0013, g32p_row02_traceSegment_090_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2187 13 14, g32p_row02_traceSegment_090_2187_0013, g32p_row02_traceSegment_090_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2160 27 27, g32p_row02_traceSegment_090_2160_0027, g32p_row02_traceSegment_090_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2214 13 14, g32p_row02_traceSegment_090_2214_0013, g32p_row02_traceSegment_090_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2241 13 14, g32p_row02_traceSegment_090_2241_0013, g32p_row02_traceSegment_090_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2214 27 27, g32p_row02_traceSegment_090_2214_0027, g32p_row02_traceSegment_090_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2160 54 54, g32p_row02_traceSegment_090_2160_0054, g32p_row02_traceSegment_090_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2268 13 14, g32p_row02_traceSegment_090_2268_0013, g32p_row02_traceSegment_090_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2295 13 14, g32p_row02_traceSegment_090_2295_0013, g32p_row02_traceSegment_090_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2268 27 27, g32p_row02_traceSegment_090_2268_0027, g32p_row02_traceSegment_090_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2322 13 14, g32p_row02_traceSegment_090_2322_0013, g32p_row02_traceSegment_090_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2349 13 14, g32p_row02_traceSegment_090_2349_0013, g32p_row02_traceSegment_090_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2322 27 27, g32p_row02_traceSegment_090_2322_0027, g32p_row02_traceSegment_090_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2268 54 54, g32p_row02_traceSegment_090_2268_0054, g32p_row02_traceSegment_090_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2160 108 108, g32p_row02_traceSegment_090_2160_0108, g32p_row02_traceSegment_090_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2376 13 14, g32p_row02_traceSegment_090_2376_0013, g32p_row02_traceSegment_090_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2403 13 14, g32p_row02_traceSegment_090_2403_0013, g32p_row02_traceSegment_090_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2376 27 27, g32p_row02_traceSegment_090_2376_0027, g32p_row02_traceSegment_090_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2430 13 14, g32p_row02_traceSegment_090_2430_0013, g32p_row02_traceSegment_090_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2457 13 14, g32p_row02_traceSegment_090_2457_0013, g32p_row02_traceSegment_090_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2430 27 27, g32p_row02_traceSegment_090_2430_0027, g32p_row02_traceSegment_090_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2376 54 54, g32p_row02_traceSegment_090_2376_0054, g32p_row02_traceSegment_090_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2484 13 14, g32p_row02_traceSegment_090_2484_0013, g32p_row02_traceSegment_090_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2511 13 14, g32p_row02_traceSegment_090_2511_0013, g32p_row02_traceSegment_090_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2484 27 27, g32p_row02_traceSegment_090_2484_0027, g32p_row02_traceSegment_090_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2538 13 14, g32p_row02_traceSegment_090_2538_0013, g32p_row02_traceSegment_090_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2565 13 14, g32p_row02_traceSegment_090_2565_0013, g32p_row02_traceSegment_090_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2538 27 27, g32p_row02_traceSegment_090_2538_0027, g32p_row02_traceSegment_090_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2484 54 54, g32p_row02_traceSegment_090_2484_0054, g32p_row02_traceSegment_090_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2376 108 108, g32p_row02_traceSegment_090_2376_0108, g32p_row02_traceSegment_090_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2160 216 216, g32p_row02_traceSegment_090_2160_0216, g32p_row02_traceSegment_090_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1728 432 432, g32p_row02_traceSegment_090_1728_0432, g32p_row02_traceSegment_090_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2592 13 14, g32p_row02_traceSegment_090_2592_0013, g32p_row02_traceSegment_090_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2619 13 14, g32p_row02_traceSegment_090_2619_0013, g32p_row02_traceSegment_090_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2592 27 27, g32p_row02_traceSegment_090_2592_0027, g32p_row02_traceSegment_090_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2646 13 14, g32p_row02_traceSegment_090_2646_0013, g32p_row02_traceSegment_090_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2673 13 14, g32p_row02_traceSegment_090_2673_0013, g32p_row02_traceSegment_090_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2646 27 27, g32p_row02_traceSegment_090_2646_0027, g32p_row02_traceSegment_090_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2592 54 54, g32p_row02_traceSegment_090_2592_0054, g32p_row02_traceSegment_090_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2700 13 14, g32p_row02_traceSegment_090_2700_0013, g32p_row02_traceSegment_090_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2727 13 14, g32p_row02_traceSegment_090_2727_0013, g32p_row02_traceSegment_090_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2700 27 27, g32p_row02_traceSegment_090_2700_0027, g32p_row02_traceSegment_090_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2754 13 14, g32p_row02_traceSegment_090_2754_0013, g32p_row02_traceSegment_090_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2781 13 14, g32p_row02_traceSegment_090_2781_0013, g32p_row02_traceSegment_090_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2754 27 27, g32p_row02_traceSegment_090_2754_0027, g32p_row02_traceSegment_090_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2700 54 54, g32p_row02_traceSegment_090_2700_0054, g32p_row02_traceSegment_090_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2592 108 108, g32p_row02_traceSegment_090_2592_0108, g32p_row02_traceSegment_090_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2808 13 14, g32p_row02_traceSegment_090_2808_0013, g32p_row02_traceSegment_090_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2835 13 14, g32p_row02_traceSegment_090_2835_0013, g32p_row02_traceSegment_090_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2808 27 27, g32p_row02_traceSegment_090_2808_0027, g32p_row02_traceSegment_090_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2862 13 14, g32p_row02_traceSegment_090_2862_0013, g32p_row02_traceSegment_090_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2889 13 14, g32p_row02_traceSegment_090_2889_0013, g32p_row02_traceSegment_090_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2862 27 27, g32p_row02_traceSegment_090_2862_0027, g32p_row02_traceSegment_090_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2808 54 54, g32p_row02_traceSegment_090_2808_0054, g32p_row02_traceSegment_090_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2916 13 14, g32p_row02_traceSegment_090_2916_0013, g32p_row02_traceSegment_090_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2943 13 14, g32p_row02_traceSegment_090_2943_0013, g32p_row02_traceSegment_090_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2916 27 27, g32p_row02_traceSegment_090_2916_0027, g32p_row02_traceSegment_090_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2970 13 14, g32p_row02_traceSegment_090_2970_0013, g32p_row02_traceSegment_090_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2997 13 14, g32p_row02_traceSegment_090_2997_0013, g32p_row02_traceSegment_090_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2970 27 27, g32p_row02_traceSegment_090_2970_0027, g32p_row02_traceSegment_090_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2916 54 54, g32p_row02_traceSegment_090_2916_0054, g32p_row02_traceSegment_090_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2808 108 108, g32p_row02_traceSegment_090_2808_0108, g32p_row02_traceSegment_090_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2592 216 216, g32p_row02_traceSegment_090_2592_0216, g32p_row02_traceSegment_090_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3024 13 14, g32p_row02_traceSegment_090_3024_0013, g32p_row02_traceSegment_090_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3051 13 14, g32p_row02_traceSegment_090_3051_0013, g32p_row02_traceSegment_090_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3024 27 27, g32p_row02_traceSegment_090_3024_0027, g32p_row02_traceSegment_090_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3078 13 14, g32p_row02_traceSegment_090_3078_0013, g32p_row02_traceSegment_090_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3105 13 14, g32p_row02_traceSegment_090_3105_0013, g32p_row02_traceSegment_090_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3078 27 27, g32p_row02_traceSegment_090_3078_0027, g32p_row02_traceSegment_090_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3024 54 54, g32p_row02_traceSegment_090_3024_0054, g32p_row02_traceSegment_090_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3132 13 14, g32p_row02_traceSegment_090_3132_0013, g32p_row02_traceSegment_090_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3159 13 14, g32p_row02_traceSegment_090_3159_0013, g32p_row02_traceSegment_090_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3132 27 27, g32p_row02_traceSegment_090_3132_0027, g32p_row02_traceSegment_090_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3186 13 14, g32p_row02_traceSegment_090_3186_0013, g32p_row02_traceSegment_090_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3226 14 = [0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3213 27 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3213 13 14, g32p_row02_traceSegment_090_3213_0013, g32p_row02_traceSegment_090_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3186 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3186 27 27, g32p_row02_traceSegment_090_3186_0027, g32p_row02_traceSegment_090_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 3132 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3132 54 54, g32p_row02_traceSegment_090_3132_0054, g32p_row02_traceSegment_090_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 3024 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3024 108 108, g32p_row02_traceSegment_090_3024_0108, g32p_row02_traceSegment_090_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3240 13 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3253 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3240 27 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3240 13 14, g32p_row02_traceSegment_090_3240_0013, g32p_row02_traceSegment_090_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3267 13 14, g32p_row02_traceSegment_090_3267_0013, g32p_row02_traceSegment_090_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3240 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3240 27 27, g32p_row02_traceSegment_090_3240_0027, g32p_row02_traceSegment_090_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3294 13 14, g32p_row02_traceSegment_090_3294_0013, g32p_row02_traceSegment_090_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3334 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3321 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3321 13 14, g32p_row02_traceSegment_090_3321_0013, g32p_row02_traceSegment_090_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3294 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3294 27 27, g32p_row02_traceSegment_090_3294_0027, g32p_row02_traceSegment_090_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 3240 108 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3240 54 54, g32p_row02_traceSegment_090_3240_0054, g32p_row02_traceSegment_090_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3348 13 14, g32p_row02_traceSegment_090_3348_0013, g32p_row02_traceSegment_090_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3375 13 14, g32p_row02_traceSegment_090_3375_0013, g32p_row02_traceSegment_090_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3348 27 27, g32p_row02_traceSegment_090_3348_0027, g32p_row02_traceSegment_090_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3402 13 14, g32p_row02_traceSegment_090_3402_0013, g32p_row02_traceSegment_090_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_090 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_090 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_090_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_090 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3429 13 14, g32p_row02_traceSegment_090_3429_0013, g32p_row02_traceSegment_090_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_090 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3402 27 27, g32p_row02_traceSegment_090_3402_0027, g32p_row02_traceSegment_090_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_090 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3348 54 54, g32p_row02_traceSegment_090_3348_0054, g32p_row02_traceSegment_090_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_090 3240 216 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3240 108 108, g32p_row02_traceSegment_090_3240_0108, g32p_row02_traceSegment_090_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_090_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_090 3024 432 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 3024 216 216, g32p_row02_traceSegment_090_3024_0216, g32p_row02_traceSegment_090_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_090_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_090 2592 864 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 2592 432 432, g32p_row02_traceSegment_090_2592_0432, g32p_row02_traceSegment_090_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_090_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_090 1728 1728 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 1728 864 864, g32p_row02_traceSegment_090_1728_0864, g32p_row02_traceSegment_090_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_090_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_090 0 3456 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_090 0 1728 1728, g32p_row02_traceSegment_090_0000_1728, g32p_row02_traceSegment_090_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_090 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 90 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_090_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_091 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 91 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_091_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 13 14, g32p_row02_traceSegment_091_0000_0013, g32p_row02_traceSegment_091_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 27 13 14, g32p_row02_traceSegment_091_0027_0013, g32p_row02_traceSegment_091_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 27 27, g32p_row02_traceSegment_091_0000_0027, g32p_row02_traceSegment_091_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 54 13 14, g32p_row02_traceSegment_091_0054_0013, g32p_row02_traceSegment_091_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 81 13 14, g32p_row02_traceSegment_091_0081_0013, g32p_row02_traceSegment_091_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 54 27 27, g32p_row02_traceSegment_091_0054_0027, g32p_row02_traceSegment_091_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 54 54, g32p_row02_traceSegment_091_0000_0054, g32p_row02_traceSegment_091_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 108 13 14, g32p_row02_traceSegment_091_0108_0013, g32p_row02_traceSegment_091_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 135 13 14, g32p_row02_traceSegment_091_0135_0013, g32p_row02_traceSegment_091_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 108 27 27, g32p_row02_traceSegment_091_0108_0027, g32p_row02_traceSegment_091_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 162 13 14, g32p_row02_traceSegment_091_0162_0013, g32p_row02_traceSegment_091_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 189 13 14, g32p_row02_traceSegment_091_0189_0013, g32p_row02_traceSegment_091_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 162 27 27, g32p_row02_traceSegment_091_0162_0027, g32p_row02_traceSegment_091_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 108 54 54, g32p_row02_traceSegment_091_0108_0054, g32p_row02_traceSegment_091_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 108 108, g32p_row02_traceSegment_091_0000_0108, g32p_row02_traceSegment_091_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 216 13 14, g32p_row02_traceSegment_091_0216_0013, g32p_row02_traceSegment_091_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 243 13 14, g32p_row02_traceSegment_091_0243_0013, g32p_row02_traceSegment_091_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 216 27 27, g32p_row02_traceSegment_091_0216_0027, g32p_row02_traceSegment_091_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 270 13 14, g32p_row02_traceSegment_091_0270_0013, g32p_row02_traceSegment_091_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 297 13 14, g32p_row02_traceSegment_091_0297_0013, g32p_row02_traceSegment_091_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 270 27 27, g32p_row02_traceSegment_091_0270_0027, g32p_row02_traceSegment_091_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 216 54 54, g32p_row02_traceSegment_091_0216_0054, g32p_row02_traceSegment_091_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 324 13 14, g32p_row02_traceSegment_091_0324_0013, g32p_row02_traceSegment_091_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 351 13 14, g32p_row02_traceSegment_091_0351_0013, g32p_row02_traceSegment_091_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 324 27 27, g32p_row02_traceSegment_091_0324_0027, g32p_row02_traceSegment_091_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 378 13 14, g32p_row02_traceSegment_091_0378_0013, g32p_row02_traceSegment_091_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 405 13 14, g32p_row02_traceSegment_091_0405_0013, g32p_row02_traceSegment_091_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 378 27 27, g32p_row02_traceSegment_091_0378_0027, g32p_row02_traceSegment_091_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 324 54 54, g32p_row02_traceSegment_091_0324_0054, g32p_row02_traceSegment_091_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 216 108 108, g32p_row02_traceSegment_091_0216_0108, g32p_row02_traceSegment_091_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 216 216, g32p_row02_traceSegment_091_0000_0216, g32p_row02_traceSegment_091_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 432 13 14, g32p_row02_traceSegment_091_0432_0013, g32p_row02_traceSegment_091_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 459 13 14, g32p_row02_traceSegment_091_0459_0013, g32p_row02_traceSegment_091_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 432 27 27, g32p_row02_traceSegment_091_0432_0027, g32p_row02_traceSegment_091_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 486 13 14, g32p_row02_traceSegment_091_0486_0013, g32p_row02_traceSegment_091_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 513 13 14, g32p_row02_traceSegment_091_0513_0013, g32p_row02_traceSegment_091_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 486 27 27, g32p_row02_traceSegment_091_0486_0027, g32p_row02_traceSegment_091_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 432 54 54, g32p_row02_traceSegment_091_0432_0054, g32p_row02_traceSegment_091_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 540 13 14, g32p_row02_traceSegment_091_0540_0013, g32p_row02_traceSegment_091_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 567 13 14, g32p_row02_traceSegment_091_0567_0013, g32p_row02_traceSegment_091_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 540 27 27, g32p_row02_traceSegment_091_0540_0027, g32p_row02_traceSegment_091_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 594 13 14, g32p_row02_traceSegment_091_0594_0013, g32p_row02_traceSegment_091_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 621 13 14, g32p_row02_traceSegment_091_0621_0013, g32p_row02_traceSegment_091_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 594 27 27, g32p_row02_traceSegment_091_0594_0027, g32p_row02_traceSegment_091_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 540 54 54, g32p_row02_traceSegment_091_0540_0054, g32p_row02_traceSegment_091_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 432 108 108, g32p_row02_traceSegment_091_0432_0108, g32p_row02_traceSegment_091_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 648 13 14, g32p_row02_traceSegment_091_0648_0013, g32p_row02_traceSegment_091_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 675 13 14, g32p_row02_traceSegment_091_0675_0013, g32p_row02_traceSegment_091_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 648 27 27, g32p_row02_traceSegment_091_0648_0027, g32p_row02_traceSegment_091_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 702 13 14, g32p_row02_traceSegment_091_0702_0013, g32p_row02_traceSegment_091_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 729 13 14, g32p_row02_traceSegment_091_0729_0013, g32p_row02_traceSegment_091_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 702 27 27, g32p_row02_traceSegment_091_0702_0027, g32p_row02_traceSegment_091_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 648 54 54, g32p_row02_traceSegment_091_0648_0054, g32p_row02_traceSegment_091_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 756 13 14, g32p_row02_traceSegment_091_0756_0013, g32p_row02_traceSegment_091_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 783 13 14, g32p_row02_traceSegment_091_0783_0013, g32p_row02_traceSegment_091_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 756 27 27, g32p_row02_traceSegment_091_0756_0027, g32p_row02_traceSegment_091_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 810 13 14, g32p_row02_traceSegment_091_0810_0013, g32p_row02_traceSegment_091_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 837 13 14, g32p_row02_traceSegment_091_0837_0013, g32p_row02_traceSegment_091_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 810 27 27, g32p_row02_traceSegment_091_0810_0027, g32p_row02_traceSegment_091_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 756 54 54, g32p_row02_traceSegment_091_0756_0054, g32p_row02_traceSegment_091_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 648 108 108, g32p_row02_traceSegment_091_0648_0108, g32p_row02_traceSegment_091_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 432 216 216, g32p_row02_traceSegment_091_0432_0216, g32p_row02_traceSegment_091_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_091 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 432 432, g32p_row02_traceSegment_091_0000_0432, g32p_row02_traceSegment_091_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 864 13 14, g32p_row02_traceSegment_091_0864_0013, g32p_row02_traceSegment_091_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 891 13 14, g32p_row02_traceSegment_091_0891_0013, g32p_row02_traceSegment_091_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 864 27 27, g32p_row02_traceSegment_091_0864_0027, g32p_row02_traceSegment_091_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 918 13 14, g32p_row02_traceSegment_091_0918_0013, g32p_row02_traceSegment_091_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 945 13 14, g32p_row02_traceSegment_091_0945_0013, g32p_row02_traceSegment_091_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 918 27 27, g32p_row02_traceSegment_091_0918_0027, g32p_row02_traceSegment_091_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 864 54 54, g32p_row02_traceSegment_091_0864_0054, g32p_row02_traceSegment_091_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 972 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 972 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 972 13 14, g32p_row02_traceSegment_091_0972_0013, g32p_row02_traceSegment_091_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 999 13 14, g32p_row02_traceSegment_091_0999_0013, g32p_row02_traceSegment_091_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 972 27 27, g32p_row02_traceSegment_091_0972_0027, g32p_row02_traceSegment_091_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1026 13 14, g32p_row02_traceSegment_091_1026_0013, g32p_row02_traceSegment_091_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1053 13 14, g32p_row02_traceSegment_091_1053_0013, g32p_row02_traceSegment_091_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1026 27 27, g32p_row02_traceSegment_091_1026_0027, g32p_row02_traceSegment_091_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 972 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 972 54 54, g32p_row02_traceSegment_091_0972_0054, g32p_row02_traceSegment_091_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 864 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 864 108 108, g32p_row02_traceSegment_091_0864_0108, g32p_row02_traceSegment_091_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1080 13 14, g32p_row02_traceSegment_091_1080_0013, g32p_row02_traceSegment_091_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1107 13 14, g32p_row02_traceSegment_091_1107_0013, g32p_row02_traceSegment_091_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1080 27 27, g32p_row02_traceSegment_091_1080_0027, g32p_row02_traceSegment_091_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1134 13 14, g32p_row02_traceSegment_091_1134_0013, g32p_row02_traceSegment_091_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1161 13 14, g32p_row02_traceSegment_091_1161_0013, g32p_row02_traceSegment_091_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1134 27 27, g32p_row02_traceSegment_091_1134_0027, g32p_row02_traceSegment_091_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1080 54 54, g32p_row02_traceSegment_091_1080_0054, g32p_row02_traceSegment_091_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1188 13 14, g32p_row02_traceSegment_091_1188_0013, g32p_row02_traceSegment_091_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1228 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1215 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1215 13 14, g32p_row02_traceSegment_091_1215_0013, g32p_row02_traceSegment_091_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1188 27 27, g32p_row02_traceSegment_091_1188_0027, g32p_row02_traceSegment_091_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1242 13 14, g32p_row02_traceSegment_091_1242_0013, g32p_row02_traceSegment_091_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1269 13 14, g32p_row02_traceSegment_091_1269_0013, g32p_row02_traceSegment_091_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1242 27 27, g32p_row02_traceSegment_091_1242_0027, g32p_row02_traceSegment_091_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1188 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1188 54 54, g32p_row02_traceSegment_091_1188_0054, g32p_row02_traceSegment_091_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 1080 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1080 108 108, g32p_row02_traceSegment_091_1080_0108, g32p_row02_traceSegment_091_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 864 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 864 216 216, g32p_row02_traceSegment_091_0864_0216, g32p_row02_traceSegment_091_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1296 13 14, g32p_row02_traceSegment_091_1296_0013, g32p_row02_traceSegment_091_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1323 13 14, g32p_row02_traceSegment_091_1323_0013, g32p_row02_traceSegment_091_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1296 27 27, g32p_row02_traceSegment_091_1296_0027, g32p_row02_traceSegment_091_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1350 13 14, g32p_row02_traceSegment_091_1350_0013, g32p_row02_traceSegment_091_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1377 13 14, g32p_row02_traceSegment_091_1377_0013, g32p_row02_traceSegment_091_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1350 27 27, g32p_row02_traceSegment_091_1350_0027, g32p_row02_traceSegment_091_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1296 54 54, g32p_row02_traceSegment_091_1296_0054, g32p_row02_traceSegment_091_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1404 13 14, g32p_row02_traceSegment_091_1404_0013, g32p_row02_traceSegment_091_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1431 13 14, g32p_row02_traceSegment_091_1431_0013, g32p_row02_traceSegment_091_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1404 27 27, g32p_row02_traceSegment_091_1404_0027, g32p_row02_traceSegment_091_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1458 13 14, g32p_row02_traceSegment_091_1458_0013, g32p_row02_traceSegment_091_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1485 13 14, g32p_row02_traceSegment_091_1485_0013, g32p_row02_traceSegment_091_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1458 27 27, g32p_row02_traceSegment_091_1458_0027, g32p_row02_traceSegment_091_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1404 54 54, g32p_row02_traceSegment_091_1404_0054, g32p_row02_traceSegment_091_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1296 108 108, g32p_row02_traceSegment_091_1296_0108, g32p_row02_traceSegment_091_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1512 13 14, g32p_row02_traceSegment_091_1512_0013, g32p_row02_traceSegment_091_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1539 13 14, g32p_row02_traceSegment_091_1539_0013, g32p_row02_traceSegment_091_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1512 27 27, g32p_row02_traceSegment_091_1512_0027, g32p_row02_traceSegment_091_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1566 13 14, g32p_row02_traceSegment_091_1566_0013, g32p_row02_traceSegment_091_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1593 13 14, g32p_row02_traceSegment_091_1593_0013, g32p_row02_traceSegment_091_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1566 27 27, g32p_row02_traceSegment_091_1566_0027, g32p_row02_traceSegment_091_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1512 54 54, g32p_row02_traceSegment_091_1512_0054, g32p_row02_traceSegment_091_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1633 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1620 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1620 13 14, g32p_row02_traceSegment_091_1620_0013, g32p_row02_traceSegment_091_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1647 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1647 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1647 13 14, g32p_row02_traceSegment_091_1647_0013, g32p_row02_traceSegment_091_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1620 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1620 27 27, g32p_row02_traceSegment_091_1620_0027, g32p_row02_traceSegment_091_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1674 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1674 13 14, g32p_row02_traceSegment_091_1674_0013, g32p_row02_traceSegment_091_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1701 13 14, g32p_row02_traceSegment_091_1701_0013, g32p_row02_traceSegment_091_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1674 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1674 27 27, g32p_row02_traceSegment_091_1674_0027, g32p_row02_traceSegment_091_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1620 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1620 54 54, g32p_row02_traceSegment_091_1620_0054, g32p_row02_traceSegment_091_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 1512 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1512 108 108, g32p_row02_traceSegment_091_1512_0108, g32p_row02_traceSegment_091_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 1296 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1296 216 216, g32p_row02_traceSegment_091_1296_0216, g32p_row02_traceSegment_091_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_091 864 864 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 864 432 432, g32p_row02_traceSegment_091_0864_0432, g32p_row02_traceSegment_091_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_091 0 1728 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 864 864, g32p_row02_traceSegment_091_0000_0864, g32p_row02_traceSegment_091_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1728 13 14, g32p_row02_traceSegment_091_1728_0013, g32p_row02_traceSegment_091_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1755 13 14, g32p_row02_traceSegment_091_1755_0013, g32p_row02_traceSegment_091_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1728 27 27, g32p_row02_traceSegment_091_1728_0027, g32p_row02_traceSegment_091_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1782 13 14, g32p_row02_traceSegment_091_1782_0013, g32p_row02_traceSegment_091_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1809 13 14, g32p_row02_traceSegment_091_1809_0013, g32p_row02_traceSegment_091_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1782 27 27, g32p_row02_traceSegment_091_1782_0027, g32p_row02_traceSegment_091_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1728 54 54, g32p_row02_traceSegment_091_1728_0054, g32p_row02_traceSegment_091_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1836 13 14, g32p_row02_traceSegment_091_1836_0013, g32p_row02_traceSegment_091_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1863 13 14, g32p_row02_traceSegment_091_1863_0013, g32p_row02_traceSegment_091_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1836 27 27, g32p_row02_traceSegment_091_1836_0027, g32p_row02_traceSegment_091_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1890 13 14, g32p_row02_traceSegment_091_1890_0013, g32p_row02_traceSegment_091_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1917 13 14, g32p_row02_traceSegment_091_1917_0013, g32p_row02_traceSegment_091_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1890 27 27, g32p_row02_traceSegment_091_1890_0027, g32p_row02_traceSegment_091_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1836 54 54, g32p_row02_traceSegment_091_1836_0054, g32p_row02_traceSegment_091_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1728 108 108, g32p_row02_traceSegment_091_1728_0108, g32p_row02_traceSegment_091_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1944 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1944 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1944 13 14, g32p_row02_traceSegment_091_1944_0013, g32p_row02_traceSegment_091_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1971 13 14, g32p_row02_traceSegment_091_1971_0013, g32p_row02_traceSegment_091_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1944 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1944 27 27, g32p_row02_traceSegment_091_1944_0027, g32p_row02_traceSegment_091_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1998 13 14, g32p_row02_traceSegment_091_1998_0013, g32p_row02_traceSegment_091_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2025 13 14, g32p_row02_traceSegment_091_2025_0013, g32p_row02_traceSegment_091_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1998 27 27, g32p_row02_traceSegment_091_1998_0027, g32p_row02_traceSegment_091_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 1944 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1944 54 54, g32p_row02_traceSegment_091_1944_0054, g32p_row02_traceSegment_091_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2052 13 14, g32p_row02_traceSegment_091_2052_0013, g32p_row02_traceSegment_091_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2079 13 14, g32p_row02_traceSegment_091_2079_0013, g32p_row02_traceSegment_091_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2052 27 27, g32p_row02_traceSegment_091_2052_0027, g32p_row02_traceSegment_091_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2106 13 14, g32p_row02_traceSegment_091_2106_0013, g32p_row02_traceSegment_091_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2133 13 14, g32p_row02_traceSegment_091_2133_0013, g32p_row02_traceSegment_091_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2106 27 27, g32p_row02_traceSegment_091_2106_0027, g32p_row02_traceSegment_091_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2052 54 54, g32p_row02_traceSegment_091_2052_0054, g32p_row02_traceSegment_091_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 1944 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1944 108 108, g32p_row02_traceSegment_091_1944_0108, g32p_row02_traceSegment_091_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1728 216 216, g32p_row02_traceSegment_091_1728_0216, g32p_row02_traceSegment_091_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2160 13 14, g32p_row02_traceSegment_091_2160_0013, g32p_row02_traceSegment_091_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2187 13 14, g32p_row02_traceSegment_091_2187_0013, g32p_row02_traceSegment_091_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2160 27 27, g32p_row02_traceSegment_091_2160_0027, g32p_row02_traceSegment_091_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2214 13 14, g32p_row02_traceSegment_091_2214_0013, g32p_row02_traceSegment_091_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2241 13 14, g32p_row02_traceSegment_091_2241_0013, g32p_row02_traceSegment_091_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2214 27 27, g32p_row02_traceSegment_091_2214_0027, g32p_row02_traceSegment_091_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2160 54 54, g32p_row02_traceSegment_091_2160_0054, g32p_row02_traceSegment_091_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2268 13 14, g32p_row02_traceSegment_091_2268_0013, g32p_row02_traceSegment_091_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2295 13 14, g32p_row02_traceSegment_091_2295_0013, g32p_row02_traceSegment_091_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2268 27 27, g32p_row02_traceSegment_091_2268_0027, g32p_row02_traceSegment_091_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2322 13 14, g32p_row02_traceSegment_091_2322_0013, g32p_row02_traceSegment_091_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2349 13 14, g32p_row02_traceSegment_091_2349_0013, g32p_row02_traceSegment_091_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2322 27 27, g32p_row02_traceSegment_091_2322_0027, g32p_row02_traceSegment_091_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2268 54 54, g32p_row02_traceSegment_091_2268_0054, g32p_row02_traceSegment_091_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2160 108 108, g32p_row02_traceSegment_091_2160_0108, g32p_row02_traceSegment_091_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2376 13 14, g32p_row02_traceSegment_091_2376_0013, g32p_row02_traceSegment_091_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2403 13 14, g32p_row02_traceSegment_091_2403_0013, g32p_row02_traceSegment_091_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2376 27 27, g32p_row02_traceSegment_091_2376_0027, g32p_row02_traceSegment_091_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2430 13 14, g32p_row02_traceSegment_091_2430_0013, g32p_row02_traceSegment_091_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2457 13 14, g32p_row02_traceSegment_091_2457_0013, g32p_row02_traceSegment_091_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2430 27 27, g32p_row02_traceSegment_091_2430_0027, g32p_row02_traceSegment_091_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2376 54 54, g32p_row02_traceSegment_091_2376_0054, g32p_row02_traceSegment_091_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2484 13 14, g32p_row02_traceSegment_091_2484_0013, g32p_row02_traceSegment_091_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2511 13 14, g32p_row02_traceSegment_091_2511_0013, g32p_row02_traceSegment_091_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2484 27 27, g32p_row02_traceSegment_091_2484_0027, g32p_row02_traceSegment_091_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2538 13 14, g32p_row02_traceSegment_091_2538_0013, g32p_row02_traceSegment_091_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2565 13 14, g32p_row02_traceSegment_091_2565_0013, g32p_row02_traceSegment_091_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2538 27 27, g32p_row02_traceSegment_091_2538_0027, g32p_row02_traceSegment_091_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2484 54 54, g32p_row02_traceSegment_091_2484_0054, g32p_row02_traceSegment_091_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2376 108 108, g32p_row02_traceSegment_091_2376_0108, g32p_row02_traceSegment_091_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2160 216 216, g32p_row02_traceSegment_091_2160_0216, g32p_row02_traceSegment_091_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1728 432 432, g32p_row02_traceSegment_091_1728_0432, g32p_row02_traceSegment_091_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2592 13 14, g32p_row02_traceSegment_091_2592_0013, g32p_row02_traceSegment_091_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2619 13 14, g32p_row02_traceSegment_091_2619_0013, g32p_row02_traceSegment_091_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2592 27 27, g32p_row02_traceSegment_091_2592_0027, g32p_row02_traceSegment_091_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2646 13 14, g32p_row02_traceSegment_091_2646_0013, g32p_row02_traceSegment_091_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2673 13 14, g32p_row02_traceSegment_091_2673_0013, g32p_row02_traceSegment_091_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2646 27 27, g32p_row02_traceSegment_091_2646_0027, g32p_row02_traceSegment_091_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2592 54 54, g32p_row02_traceSegment_091_2592_0054, g32p_row02_traceSegment_091_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2700 13 14, g32p_row02_traceSegment_091_2700_0013, g32p_row02_traceSegment_091_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2727 13 14, g32p_row02_traceSegment_091_2727_0013, g32p_row02_traceSegment_091_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2700 27 27, g32p_row02_traceSegment_091_2700_0027, g32p_row02_traceSegment_091_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2754 13 14, g32p_row02_traceSegment_091_2754_0013, g32p_row02_traceSegment_091_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2781 13 14, g32p_row02_traceSegment_091_2781_0013, g32p_row02_traceSegment_091_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2754 27 27, g32p_row02_traceSegment_091_2754_0027, g32p_row02_traceSegment_091_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2700 54 54, g32p_row02_traceSegment_091_2700_0054, g32p_row02_traceSegment_091_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2592 108 108, g32p_row02_traceSegment_091_2592_0108, g32p_row02_traceSegment_091_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2808 13 14, g32p_row02_traceSegment_091_2808_0013, g32p_row02_traceSegment_091_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2835 13 14, g32p_row02_traceSegment_091_2835_0013, g32p_row02_traceSegment_091_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2808 27 27, g32p_row02_traceSegment_091_2808_0027, g32p_row02_traceSegment_091_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2862 13 14, g32p_row02_traceSegment_091_2862_0013, g32p_row02_traceSegment_091_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2889 13 14, g32p_row02_traceSegment_091_2889_0013, g32p_row02_traceSegment_091_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2862 27 27, g32p_row02_traceSegment_091_2862_0027, g32p_row02_traceSegment_091_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2808 54 54, g32p_row02_traceSegment_091_2808_0054, g32p_row02_traceSegment_091_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2916 13 14, g32p_row02_traceSegment_091_2916_0013, g32p_row02_traceSegment_091_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2943 13 14, g32p_row02_traceSegment_091_2943_0013, g32p_row02_traceSegment_091_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2916 27 27, g32p_row02_traceSegment_091_2916_0027, g32p_row02_traceSegment_091_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2970 13 14, g32p_row02_traceSegment_091_2970_0013, g32p_row02_traceSegment_091_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2997 13 14, g32p_row02_traceSegment_091_2997_0013, g32p_row02_traceSegment_091_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2970 27 27, g32p_row02_traceSegment_091_2970_0027, g32p_row02_traceSegment_091_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2916 54 54, g32p_row02_traceSegment_091_2916_0054, g32p_row02_traceSegment_091_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2808 108 108, g32p_row02_traceSegment_091_2808_0108, g32p_row02_traceSegment_091_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2592 216 216, g32p_row02_traceSegment_091_2592_0216, g32p_row02_traceSegment_091_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3024 13 14, g32p_row02_traceSegment_091_3024_0013, g32p_row02_traceSegment_091_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3051 13 14, g32p_row02_traceSegment_091_3051_0013, g32p_row02_traceSegment_091_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3024 27 27, g32p_row02_traceSegment_091_3024_0027, g32p_row02_traceSegment_091_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3078 13 14, g32p_row02_traceSegment_091_3078_0013, g32p_row02_traceSegment_091_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3105 13 14, g32p_row02_traceSegment_091_3105_0013, g32p_row02_traceSegment_091_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3078 27 27, g32p_row02_traceSegment_091_3078_0027, g32p_row02_traceSegment_091_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3024 54 54, g32p_row02_traceSegment_091_3024_0054, g32p_row02_traceSegment_091_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3132 13 14, g32p_row02_traceSegment_091_3132_0013, g32p_row02_traceSegment_091_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3159 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3159 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3159 13 14, g32p_row02_traceSegment_091_3159_0013, g32p_row02_traceSegment_091_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3132 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3132 27 27, g32p_row02_traceSegment_091_3132_0027, g32p_row02_traceSegment_091_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3186 13 14, g32p_row02_traceSegment_091_3186_0013, g32p_row02_traceSegment_091_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3213 13 14, g32p_row02_traceSegment_091_3213_0013, g32p_row02_traceSegment_091_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3186 27 27, g32p_row02_traceSegment_091_3186_0027, g32p_row02_traceSegment_091_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3132 54 54, g32p_row02_traceSegment_091_3132_0054, g32p_row02_traceSegment_091_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 3024 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3024 108 108, g32p_row02_traceSegment_091_3024_0108, g32p_row02_traceSegment_091_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3240 13 14, g32p_row02_traceSegment_091_3240_0013, g32p_row02_traceSegment_091_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3267 13 14, g32p_row02_traceSegment_091_3267_0013, g32p_row02_traceSegment_091_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3240 27 27, g32p_row02_traceSegment_091_3240_0027, g32p_row02_traceSegment_091_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3294 13 14, g32p_row02_traceSegment_091_3294_0013, g32p_row02_traceSegment_091_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3321 13 14, g32p_row02_traceSegment_091_3321_0013, g32p_row02_traceSegment_091_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3294 27 27, g32p_row02_traceSegment_091_3294_0027, g32p_row02_traceSegment_091_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3240 54 54, g32p_row02_traceSegment_091_3240_0054, g32p_row02_traceSegment_091_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3348 13 14, g32p_row02_traceSegment_091_3348_0013, g32p_row02_traceSegment_091_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3375 13 14, g32p_row02_traceSegment_091_3375_0013, g32p_row02_traceSegment_091_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3348 27 27, g32p_row02_traceSegment_091_3348_0027, g32p_row02_traceSegment_091_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3402 13 14, g32p_row02_traceSegment_091_3402_0013, g32p_row02_traceSegment_091_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_091 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_091 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_091_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_091 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3429 13 14, g32p_row02_traceSegment_091_3429_0013, g32p_row02_traceSegment_091_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_091 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3402 27 27, g32p_row02_traceSegment_091_3402_0027, g32p_row02_traceSegment_091_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_091 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3348 54 54, g32p_row02_traceSegment_091_3348_0054, g32p_row02_traceSegment_091_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_091 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3240 108 108, g32p_row02_traceSegment_091_3240_0108, g32p_row02_traceSegment_091_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_091_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_091 3024 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 3024 216 216, g32p_row02_traceSegment_091_3024_0216, g32p_row02_traceSegment_091_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_091_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_091 2592 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 2592 432 432, g32p_row02_traceSegment_091_2592_0432, g32p_row02_traceSegment_091_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_091_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_091 1728 1728 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 1728 864 864, g32p_row02_traceSegment_091_1728_0864, g32p_row02_traceSegment_091_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_091_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_091 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_091 0 1728 1728, g32p_row02_traceSegment_091_0000_1728, g32p_row02_traceSegment_091_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_091 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 91 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_091_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_092_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 13 14, g32p_row02_traceSegment_092_0000_0013, g32p_row02_traceSegment_092_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 27 13 14, g32p_row02_traceSegment_092_0027_0013, g32p_row02_traceSegment_092_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 27 27, g32p_row02_traceSegment_092_0000_0027, g32p_row02_traceSegment_092_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 54 13 14, g32p_row02_traceSegment_092_0054_0013, g32p_row02_traceSegment_092_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 81 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 94 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 81 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 81 13 14, g32p_row02_traceSegment_092_0081_0013, g32p_row02_traceSegment_092_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 54 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 54 27 27, g32p_row02_traceSegment_092_0054_0027, g32p_row02_traceSegment_092_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 0 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 54 54, g32p_row02_traceSegment_092_0000_0054, g32p_row02_traceSegment_092_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 108 13 14, g32p_row02_traceSegment_092_0108_0013, g32p_row02_traceSegment_092_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 135 13 14, g32p_row02_traceSegment_092_0135_0013, g32p_row02_traceSegment_092_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 108 27 27, g32p_row02_traceSegment_092_0108_0027, g32p_row02_traceSegment_092_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 162 13 14, g32p_row02_traceSegment_092_0162_0013, g32p_row02_traceSegment_092_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 189 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 189 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 189 13 14, g32p_row02_traceSegment_092_0189_0013, g32p_row02_traceSegment_092_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 162 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 162 27 27, g32p_row02_traceSegment_092_0162_0027, g32p_row02_traceSegment_092_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 108 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 108 54 54, g32p_row02_traceSegment_092_0108_0054, g32p_row02_traceSegment_092_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 0 216 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 108 108, g32p_row02_traceSegment_092_0000_0108, g32p_row02_traceSegment_092_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 216 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 216 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 216 13 14, g32p_row02_traceSegment_092_0216_0013, g32p_row02_traceSegment_092_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 243 13 14, g32p_row02_traceSegment_092_0243_0013, g32p_row02_traceSegment_092_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 216 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 216 27 27, g32p_row02_traceSegment_092_0216_0027, g32p_row02_traceSegment_092_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 270 13 14, g32p_row02_traceSegment_092_0270_0013, g32p_row02_traceSegment_092_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 297 13 14, g32p_row02_traceSegment_092_0297_0013, g32p_row02_traceSegment_092_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 270 27 27, g32p_row02_traceSegment_092_0270_0027, g32p_row02_traceSegment_092_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 216 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 216 54 54, g32p_row02_traceSegment_092_0216_0054, g32p_row02_traceSegment_092_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 324 13 14, g32p_row02_traceSegment_092_0324_0013, g32p_row02_traceSegment_092_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 351 13 14, g32p_row02_traceSegment_092_0351_0013, g32p_row02_traceSegment_092_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 324 27 27, g32p_row02_traceSegment_092_0324_0027, g32p_row02_traceSegment_092_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 378 13 14, g32p_row02_traceSegment_092_0378_0013, g32p_row02_traceSegment_092_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 405 13 14, g32p_row02_traceSegment_092_0405_0013, g32p_row02_traceSegment_092_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 378 27 27, g32p_row02_traceSegment_092_0378_0027, g32p_row02_traceSegment_092_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 324 54 54, g32p_row02_traceSegment_092_0324_0054, g32p_row02_traceSegment_092_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 216 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 216 108 108, g32p_row02_traceSegment_092_0216_0108, g32p_row02_traceSegment_092_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 0 432 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 216 216, g32p_row02_traceSegment_092_0000_0216, g32p_row02_traceSegment_092_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 432 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 432 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 432 13 14, g32p_row02_traceSegment_092_0432_0013, g32p_row02_traceSegment_092_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 459 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 459 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 459 13 14, g32p_row02_traceSegment_092_0459_0013, g32p_row02_traceSegment_092_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 432 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 432 27 27, g32p_row02_traceSegment_092_0432_0027, g32p_row02_traceSegment_092_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 486 13 14, g32p_row02_traceSegment_092_0486_0013, g32p_row02_traceSegment_092_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 513 13 14, g32p_row02_traceSegment_092_0513_0013, g32p_row02_traceSegment_092_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 486 27 27, g32p_row02_traceSegment_092_0486_0027, g32p_row02_traceSegment_092_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 432 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 432 54 54, g32p_row02_traceSegment_092_0432_0054, g32p_row02_traceSegment_092_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 540 13 14, g32p_row02_traceSegment_092_0540_0013, g32p_row02_traceSegment_092_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 567 13 14, g32p_row02_traceSegment_092_0567_0013, g32p_row02_traceSegment_092_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 540 27 27, g32p_row02_traceSegment_092_0540_0027, g32p_row02_traceSegment_092_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 594 13 14, g32p_row02_traceSegment_092_0594_0013, g32p_row02_traceSegment_092_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 621 13 14, g32p_row02_traceSegment_092_0621_0013, g32p_row02_traceSegment_092_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 594 27 27, g32p_row02_traceSegment_092_0594_0027, g32p_row02_traceSegment_092_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 540 54 54, g32p_row02_traceSegment_092_0540_0054, g32p_row02_traceSegment_092_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 432 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 432 108 108, g32p_row02_traceSegment_092_0432_0108, g32p_row02_traceSegment_092_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 648 13 14, g32p_row02_traceSegment_092_0648_0013, g32p_row02_traceSegment_092_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 675 13 14, g32p_row02_traceSegment_092_0675_0013, g32p_row02_traceSegment_092_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 648 27 27, g32p_row02_traceSegment_092_0648_0027, g32p_row02_traceSegment_092_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 702 13 14, g32p_row02_traceSegment_092_0702_0013, g32p_row02_traceSegment_092_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 729 13 14, g32p_row02_traceSegment_092_0729_0013, g32p_row02_traceSegment_092_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 702 27 27, g32p_row02_traceSegment_092_0702_0027, g32p_row02_traceSegment_092_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 648 54 54, g32p_row02_traceSegment_092_0648_0054, g32p_row02_traceSegment_092_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 756 13 14, g32p_row02_traceSegment_092_0756_0013, g32p_row02_traceSegment_092_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 783 13 14, g32p_row02_traceSegment_092_0783_0013, g32p_row02_traceSegment_092_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 756 27 27, g32p_row02_traceSegment_092_0756_0027, g32p_row02_traceSegment_092_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 810 13 14, g32p_row02_traceSegment_092_0810_0013, g32p_row02_traceSegment_092_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 837 13 14, g32p_row02_traceSegment_092_0837_0013, g32p_row02_traceSegment_092_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 810 27 27, g32p_row02_traceSegment_092_0810_0027, g32p_row02_traceSegment_092_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 756 54 54, g32p_row02_traceSegment_092_0756_0054, g32p_row02_traceSegment_092_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 648 108 108, g32p_row02_traceSegment_092_0648_0108, g32p_row02_traceSegment_092_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 432 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 432 216 216, g32p_row02_traceSegment_092_0432_0216, g32p_row02_traceSegment_092_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_092 0 864 = [2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 432 432, g32p_row02_traceSegment_092_0000_0432, g32p_row02_traceSegment_092_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 864 13 14, g32p_row02_traceSegment_092_0864_0013, g32p_row02_traceSegment_092_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 891 13 14, g32p_row02_traceSegment_092_0891_0013, g32p_row02_traceSegment_092_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 864 27 27, g32p_row02_traceSegment_092_0864_0027, g32p_row02_traceSegment_092_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 918 13 14, g32p_row02_traceSegment_092_0918_0013, g32p_row02_traceSegment_092_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 945 13 14, g32p_row02_traceSegment_092_0945_0013, g32p_row02_traceSegment_092_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 918 27 27, g32p_row02_traceSegment_092_0918_0027, g32p_row02_traceSegment_092_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 864 54 54, g32p_row02_traceSegment_092_0864_0054, g32p_row02_traceSegment_092_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 972 13 14, g32p_row02_traceSegment_092_0972_0013, g32p_row02_traceSegment_092_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 999 13 14, g32p_row02_traceSegment_092_0999_0013, g32p_row02_traceSegment_092_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 972 27 27, g32p_row02_traceSegment_092_0972_0027, g32p_row02_traceSegment_092_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1026 13 14, g32p_row02_traceSegment_092_1026_0013, g32p_row02_traceSegment_092_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1066 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1053 13 14, g32p_row02_traceSegment_092_1053_0013, g32p_row02_traceSegment_092_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1026 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1026 27 27, g32p_row02_traceSegment_092_1026_0027, g32p_row02_traceSegment_092_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 972 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 972 54 54, g32p_row02_traceSegment_092_0972_0054, g32p_row02_traceSegment_092_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 864 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 864 108 108, g32p_row02_traceSegment_092_0864_0108, g32p_row02_traceSegment_092_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1080 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1080 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1080 13 14, g32p_row02_traceSegment_092_1080_0013, g32p_row02_traceSegment_092_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1107 13 14, g32p_row02_traceSegment_092_1107_0013, g32p_row02_traceSegment_092_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1080 27 27, g32p_row02_traceSegment_092_1080_0027, g32p_row02_traceSegment_092_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1134 13 14, g32p_row02_traceSegment_092_1134_0013, g32p_row02_traceSegment_092_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1161 13 14, g32p_row02_traceSegment_092_1161_0013, g32p_row02_traceSegment_092_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1134 27 27, g32p_row02_traceSegment_092_1134_0027, g32p_row02_traceSegment_092_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1080 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1080 54 54, g32p_row02_traceSegment_092_1080_0054, g32p_row02_traceSegment_092_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1188 13 14, g32p_row02_traceSegment_092_1188_0013, g32p_row02_traceSegment_092_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1215 13 14, g32p_row02_traceSegment_092_1215_0013, g32p_row02_traceSegment_092_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1188 27 27, g32p_row02_traceSegment_092_1188_0027, g32p_row02_traceSegment_092_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1242 13 14, g32p_row02_traceSegment_092_1242_0013, g32p_row02_traceSegment_092_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1269 13 14, g32p_row02_traceSegment_092_1269_0013, g32p_row02_traceSegment_092_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1242 27 27, g32p_row02_traceSegment_092_1242_0027, g32p_row02_traceSegment_092_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1188 54 54, g32p_row02_traceSegment_092_1188_0054, g32p_row02_traceSegment_092_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1080 108 108, g32p_row02_traceSegment_092_1080_0108, g32p_row02_traceSegment_092_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 864 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 864 216 216, g32p_row02_traceSegment_092_0864_0216, g32p_row02_traceSegment_092_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1309 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1296 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1296 13 14, g32p_row02_traceSegment_092_1296_0013, g32p_row02_traceSegment_092_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1323 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1323 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1323 13 14, g32p_row02_traceSegment_092_1323_0013, g32p_row02_traceSegment_092_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1296 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1296 27 27, g32p_row02_traceSegment_092_1296_0027, g32p_row02_traceSegment_092_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1350 13 14, g32p_row02_traceSegment_092_1350_0013, g32p_row02_traceSegment_092_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1377 13 14, g32p_row02_traceSegment_092_1377_0013, g32p_row02_traceSegment_092_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1350 27 27, g32p_row02_traceSegment_092_1350_0027, g32p_row02_traceSegment_092_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1296 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1296 54 54, g32p_row02_traceSegment_092_1296_0054, g32p_row02_traceSegment_092_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1417 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1404 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1404 13 14, g32p_row02_traceSegment_092_1404_0013, g32p_row02_traceSegment_092_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1431 13 14, g32p_row02_traceSegment_092_1431_0013, g32p_row02_traceSegment_092_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1404 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1404 27 27, g32p_row02_traceSegment_092_1404_0027, g32p_row02_traceSegment_092_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1471 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1458 27 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1458 13 14, g32p_row02_traceSegment_092_1458_0013, g32p_row02_traceSegment_092_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1485 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1498 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1485 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1485 13 14, g32p_row02_traceSegment_092_1485_0013, g32p_row02_traceSegment_092_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1458 54 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1458 27 27, g32p_row02_traceSegment_092_1458_0027, g32p_row02_traceSegment_092_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1404 108 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1404 54 54, g32p_row02_traceSegment_092_1404_0054, g32p_row02_traceSegment_092_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 1296 216 = [1, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1296 108 108, g32p_row02_traceSegment_092_1296_0108, g32p_row02_traceSegment_092_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1525 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1512 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1512 13 14, g32p_row02_traceSegment_092_1512_0013, g32p_row02_traceSegment_092_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1539 13 14, g32p_row02_traceSegment_092_1539_0013, g32p_row02_traceSegment_092_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1512 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1512 27 27, g32p_row02_traceSegment_092_1512_0027, g32p_row02_traceSegment_092_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1566 13 14, g32p_row02_traceSegment_092_1566_0013, g32p_row02_traceSegment_092_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1593 13 14, g32p_row02_traceSegment_092_1593_0013, g32p_row02_traceSegment_092_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1566 27 27, g32p_row02_traceSegment_092_1566_0027, g32p_row02_traceSegment_092_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1512 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1512 54 54, g32p_row02_traceSegment_092_1512_0054, g32p_row02_traceSegment_092_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1620 13 14, g32p_row02_traceSegment_092_1620_0013, g32p_row02_traceSegment_092_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1647 13 14, g32p_row02_traceSegment_092_1647_0013, g32p_row02_traceSegment_092_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1620 27 27, g32p_row02_traceSegment_092_1620_0027, g32p_row02_traceSegment_092_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1674 13 14, g32p_row02_traceSegment_092_1674_0013, g32p_row02_traceSegment_092_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1701 13 14, g32p_row02_traceSegment_092_1701_0013, g32p_row02_traceSegment_092_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1674 27 27, g32p_row02_traceSegment_092_1674_0027, g32p_row02_traceSegment_092_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1620 54 54, g32p_row02_traceSegment_092_1620_0054, g32p_row02_traceSegment_092_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 1512 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1512 108 108, g32p_row02_traceSegment_092_1512_0108, g32p_row02_traceSegment_092_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 1296 432 = [2, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1296 216 216, g32p_row02_traceSegment_092_1296_0216, g32p_row02_traceSegment_092_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_092 864 864 = [2, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 864 432 432, g32p_row02_traceSegment_092_0864_0432, g32p_row02_traceSegment_092_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_092 0 1728 = [4, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 864 864, g32p_row02_traceSegment_092_0000_0864, g32p_row02_traceSegment_092_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1728 13 14, g32p_row02_traceSegment_092_1728_0013, g32p_row02_traceSegment_092_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1768 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1755 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1755 13 14, g32p_row02_traceSegment_092_1755_0013, g32p_row02_traceSegment_092_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1728 27 27, g32p_row02_traceSegment_092_1728_0027, g32p_row02_traceSegment_092_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1782 13 14, g32p_row02_traceSegment_092_1782_0013, g32p_row02_traceSegment_092_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1809 13 14, g32p_row02_traceSegment_092_1809_0013, g32p_row02_traceSegment_092_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1782 27 27, g32p_row02_traceSegment_092_1782_0027, g32p_row02_traceSegment_092_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1728 54 54, g32p_row02_traceSegment_092_1728_0054, g32p_row02_traceSegment_092_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1836 13 14, g32p_row02_traceSegment_092_1836_0013, g32p_row02_traceSegment_092_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1863 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1863 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1863 13 14, g32p_row02_traceSegment_092_1863_0013, g32p_row02_traceSegment_092_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1836 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1836 27 27, g32p_row02_traceSegment_092_1836_0027, g32p_row02_traceSegment_092_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1890 13 14, g32p_row02_traceSegment_092_1890_0013, g32p_row02_traceSegment_092_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1930 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1917 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1917 13 14, g32p_row02_traceSegment_092_1917_0013, g32p_row02_traceSegment_092_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1890 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1890 27 27, g32p_row02_traceSegment_092_1890_0027, g32p_row02_traceSegment_092_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1836 108 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1836 54 54, g32p_row02_traceSegment_092_1836_0054, g32p_row02_traceSegment_092_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 216 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1728 108 108, g32p_row02_traceSegment_092_1728_0108, g32p_row02_traceSegment_092_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1944 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1944 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1944 13 14, g32p_row02_traceSegment_092_1944_0013, g32p_row02_traceSegment_092_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1971 13 14, g32p_row02_traceSegment_092_1971_0013, g32p_row02_traceSegment_092_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1944 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1944 27 27, g32p_row02_traceSegment_092_1944_0027, g32p_row02_traceSegment_092_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1998 13 14, g32p_row02_traceSegment_092_1998_0013, g32p_row02_traceSegment_092_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2025 13 14, g32p_row02_traceSegment_092_2025_0013, g32p_row02_traceSegment_092_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1998 27 27, g32p_row02_traceSegment_092_1998_0027, g32p_row02_traceSegment_092_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 1944 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1944 54 54, g32p_row02_traceSegment_092_1944_0054, g32p_row02_traceSegment_092_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2052 13 14, g32p_row02_traceSegment_092_2052_0013, g32p_row02_traceSegment_092_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2079 13 14, g32p_row02_traceSegment_092_2079_0013, g32p_row02_traceSegment_092_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2052 27 27, g32p_row02_traceSegment_092_2052_0027, g32p_row02_traceSegment_092_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2106 13 14, g32p_row02_traceSegment_092_2106_0013, g32p_row02_traceSegment_092_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2133 13 14, g32p_row02_traceSegment_092_2133_0013, g32p_row02_traceSegment_092_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2106 27 27, g32p_row02_traceSegment_092_2106_0027, g32p_row02_traceSegment_092_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2052 54 54, g32p_row02_traceSegment_092_2052_0054, g32p_row02_traceSegment_092_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 1944 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1944 108 108, g32p_row02_traceSegment_092_1944_0108, g32p_row02_traceSegment_092_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 432 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1728 216 216, g32p_row02_traceSegment_092_1728_0216, g32p_row02_traceSegment_092_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2160 13 14, g32p_row02_traceSegment_092_2160_0013, g32p_row02_traceSegment_092_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2187 13 14, g32p_row02_traceSegment_092_2187_0013, g32p_row02_traceSegment_092_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2160 27 27, g32p_row02_traceSegment_092_2160_0027, g32p_row02_traceSegment_092_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2214 13 14, g32p_row02_traceSegment_092_2214_0013, g32p_row02_traceSegment_092_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2241 13 14, g32p_row02_traceSegment_092_2241_0013, g32p_row02_traceSegment_092_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2214 27 27, g32p_row02_traceSegment_092_2214_0027, g32p_row02_traceSegment_092_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2160 54 54, g32p_row02_traceSegment_092_2160_0054, g32p_row02_traceSegment_092_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2268 13 14, g32p_row02_traceSegment_092_2268_0013, g32p_row02_traceSegment_092_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2295 13 14, g32p_row02_traceSegment_092_2295_0013, g32p_row02_traceSegment_092_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2268 27 27, g32p_row02_traceSegment_092_2268_0027, g32p_row02_traceSegment_092_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2322 13 14, g32p_row02_traceSegment_092_2322_0013, g32p_row02_traceSegment_092_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2362 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2349 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2349 13 14, g32p_row02_traceSegment_092_2349_0013, g32p_row02_traceSegment_092_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2322 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2322 27 27, g32p_row02_traceSegment_092_2322_0027, g32p_row02_traceSegment_092_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2268 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2268 54 54, g32p_row02_traceSegment_092_2268_0054, g32p_row02_traceSegment_092_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 2160 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2160 108 108, g32p_row02_traceSegment_092_2160_0108, g32p_row02_traceSegment_092_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2389 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2376 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2376 13 14, g32p_row02_traceSegment_092_2376_0013, g32p_row02_traceSegment_092_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2403 13 14, g32p_row02_traceSegment_092_2403_0013, g32p_row02_traceSegment_092_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2376 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2376 27 27, g32p_row02_traceSegment_092_2376_0027, g32p_row02_traceSegment_092_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2430 13 14, g32p_row02_traceSegment_092_2430_0013, g32p_row02_traceSegment_092_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2457 13 14, g32p_row02_traceSegment_092_2457_0013, g32p_row02_traceSegment_092_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2430 27 27, g32p_row02_traceSegment_092_2430_0027, g32p_row02_traceSegment_092_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2376 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2376 54 54, g32p_row02_traceSegment_092_2376_0054, g32p_row02_traceSegment_092_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2484 13 14, g32p_row02_traceSegment_092_2484_0013, g32p_row02_traceSegment_092_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2511 13 14, g32p_row02_traceSegment_092_2511_0013, g32p_row02_traceSegment_092_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2484 27 27, g32p_row02_traceSegment_092_2484_0027, g32p_row02_traceSegment_092_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2538 13 14, g32p_row02_traceSegment_092_2538_0013, g32p_row02_traceSegment_092_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2565 13 14, g32p_row02_traceSegment_092_2565_0013, g32p_row02_traceSegment_092_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2538 27 27, g32p_row02_traceSegment_092_2538_0027, g32p_row02_traceSegment_092_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2484 54 54, g32p_row02_traceSegment_092_2484_0054, g32p_row02_traceSegment_092_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 2376 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2376 108 108, g32p_row02_traceSegment_092_2376_0108, g32p_row02_traceSegment_092_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 2160 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2160 216 216, g32p_row02_traceSegment_092_2160_0216, g32p_row02_traceSegment_092_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 864 = [2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1728 432 432, g32p_row02_traceSegment_092_1728_0432, g32p_row02_traceSegment_092_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2592 13 14, g32p_row02_traceSegment_092_2592_0013, g32p_row02_traceSegment_092_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2619 13 14, g32p_row02_traceSegment_092_2619_0013, g32p_row02_traceSegment_092_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2592 27 27, g32p_row02_traceSegment_092_2592_0027, g32p_row02_traceSegment_092_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2646 13 14, g32p_row02_traceSegment_092_2646_0013, g32p_row02_traceSegment_092_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2673 13 14, g32p_row02_traceSegment_092_2673_0013, g32p_row02_traceSegment_092_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2646 27 27, g32p_row02_traceSegment_092_2646_0027, g32p_row02_traceSegment_092_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2592 54 54, g32p_row02_traceSegment_092_2592_0054, g32p_row02_traceSegment_092_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2700 13 14, g32p_row02_traceSegment_092_2700_0013, g32p_row02_traceSegment_092_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2727 13 14, g32p_row02_traceSegment_092_2727_0013, g32p_row02_traceSegment_092_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2700 27 27, g32p_row02_traceSegment_092_2700_0027, g32p_row02_traceSegment_092_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2754 13 14, g32p_row02_traceSegment_092_2754_0013, g32p_row02_traceSegment_092_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2781 13 14, g32p_row02_traceSegment_092_2781_0013, g32p_row02_traceSegment_092_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2754 27 27, g32p_row02_traceSegment_092_2754_0027, g32p_row02_traceSegment_092_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2700 54 54, g32p_row02_traceSegment_092_2700_0054, g32p_row02_traceSegment_092_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2592 108 108, g32p_row02_traceSegment_092_2592_0108, g32p_row02_traceSegment_092_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2808 13 14, g32p_row02_traceSegment_092_2808_0013, g32p_row02_traceSegment_092_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2835 13 14, g32p_row02_traceSegment_092_2835_0013, g32p_row02_traceSegment_092_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2808 27 27, g32p_row02_traceSegment_092_2808_0027, g32p_row02_traceSegment_092_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2862 13 14, g32p_row02_traceSegment_092_2862_0013, g32p_row02_traceSegment_092_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2889 13 14, g32p_row02_traceSegment_092_2889_0013, g32p_row02_traceSegment_092_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2862 27 27, g32p_row02_traceSegment_092_2862_0027, g32p_row02_traceSegment_092_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2808 54 54, g32p_row02_traceSegment_092_2808_0054, g32p_row02_traceSegment_092_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2916 13 14, g32p_row02_traceSegment_092_2916_0013, g32p_row02_traceSegment_092_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2943 13 14, g32p_row02_traceSegment_092_2943_0013, g32p_row02_traceSegment_092_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2916 27 27, g32p_row02_traceSegment_092_2916_0027, g32p_row02_traceSegment_092_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2970 13 14, g32p_row02_traceSegment_092_2970_0013, g32p_row02_traceSegment_092_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2997 13 14, g32p_row02_traceSegment_092_2997_0013, g32p_row02_traceSegment_092_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2970 27 27, g32p_row02_traceSegment_092_2970_0027, g32p_row02_traceSegment_092_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2916 54 54, g32p_row02_traceSegment_092_2916_0054, g32p_row02_traceSegment_092_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2808 108 108, g32p_row02_traceSegment_092_2808_0108, g32p_row02_traceSegment_092_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2592 216 216, g32p_row02_traceSegment_092_2592_0216, g32p_row02_traceSegment_092_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3024 13 14, g32p_row02_traceSegment_092_3024_0013, g32p_row02_traceSegment_092_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3051 13 14, g32p_row02_traceSegment_092_3051_0013, g32p_row02_traceSegment_092_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3024 27 27, g32p_row02_traceSegment_092_3024_0027, g32p_row02_traceSegment_092_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3078 13 14, g32p_row02_traceSegment_092_3078_0013, g32p_row02_traceSegment_092_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3105 13 14, g32p_row02_traceSegment_092_3105_0013, g32p_row02_traceSegment_092_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3078 27 27, g32p_row02_traceSegment_092_3078_0027, g32p_row02_traceSegment_092_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3024 54 54, g32p_row02_traceSegment_092_3024_0054, g32p_row02_traceSegment_092_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3132 13 14, g32p_row02_traceSegment_092_3132_0013, g32p_row02_traceSegment_092_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3159 13 14, g32p_row02_traceSegment_092_3159_0013, g32p_row02_traceSegment_092_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3132 27 27, g32p_row02_traceSegment_092_3132_0027, g32p_row02_traceSegment_092_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3186 13 14, g32p_row02_traceSegment_092_3186_0013, g32p_row02_traceSegment_092_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3213 13 14, g32p_row02_traceSegment_092_3213_0013, g32p_row02_traceSegment_092_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3186 27 27, g32p_row02_traceSegment_092_3186_0027, g32p_row02_traceSegment_092_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3132 54 54, g32p_row02_traceSegment_092_3132_0054, g32p_row02_traceSegment_092_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3024 108 108, g32p_row02_traceSegment_092_3024_0108, g32p_row02_traceSegment_092_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3240 13 14, g32p_row02_traceSegment_092_3240_0013, g32p_row02_traceSegment_092_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3267 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3280 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3267 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3267 13 14, g32p_row02_traceSegment_092_3267_0013, g32p_row02_traceSegment_092_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3240 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3240 27 27, g32p_row02_traceSegment_092_3240_0027, g32p_row02_traceSegment_092_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3294 13 14, g32p_row02_traceSegment_092_3294_0013, g32p_row02_traceSegment_092_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3321 13 14, g32p_row02_traceSegment_092_3321_0013, g32p_row02_traceSegment_092_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3294 27 27, g32p_row02_traceSegment_092_3294_0027, g32p_row02_traceSegment_092_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 3240 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3240 54 54, g32p_row02_traceSegment_092_3240_0054, g32p_row02_traceSegment_092_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3348 13 14, g32p_row02_traceSegment_092_3348_0013, g32p_row02_traceSegment_092_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3388 14 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3375 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3375 13 14, g32p_row02_traceSegment_092_3375_0013, g32p_row02_traceSegment_092_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3348 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3348 27 27, g32p_row02_traceSegment_092_3348_0027, g32p_row02_traceSegment_092_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3402 13 = [5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3402 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3402 13 14, g32p_row02_traceSegment_092_3402_0013, g32p_row02_traceSegment_092_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_092 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_092 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_092_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_092 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3429 13 14, g32p_row02_traceSegment_092_3429_0013, g32p_row02_traceSegment_092_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_092 3402 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3402 27 27, g32p_row02_traceSegment_092_3402_0027, g32p_row02_traceSegment_092_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_092 3348 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3348 54 54, g32p_row02_traceSegment_092_3348_0054, g32p_row02_traceSegment_092_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_092 3240 216 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3240 108 108, g32p_row02_traceSegment_092_3240_0108, g32p_row02_traceSegment_092_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_092_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_092 3024 432 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 3024 216 216, g32p_row02_traceSegment_092_3024_0216, g32p_row02_traceSegment_092_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_092_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_092 2592 864 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 2592 432 432, g32p_row02_traceSegment_092_2592_0432, g32p_row02_traceSegment_092_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_092_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_092 1728 1728 = [12, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 1728 864 864, g32p_row02_traceSegment_092_1728_0864, g32p_row02_traceSegment_092_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_092_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_092 0 3456 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_092 0 1728 1728, g32p_row02_traceSegment_092_0000_1728, g32p_row02_traceSegment_092_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 92 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_092_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_093 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 93 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_093_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 13 14, g32p_row02_traceSegment_093_0000_0013, g32p_row02_traceSegment_093_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 27 13 14, g32p_row02_traceSegment_093_0027_0013, g32p_row02_traceSegment_093_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 27 27, g32p_row02_traceSegment_093_0000_0027, g32p_row02_traceSegment_093_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 54 13 14, g32p_row02_traceSegment_093_0054_0013, g32p_row02_traceSegment_093_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 81 13 14, g32p_row02_traceSegment_093_0081_0013, g32p_row02_traceSegment_093_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 54 27 27, g32p_row02_traceSegment_093_0054_0027, g32p_row02_traceSegment_093_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 54 54, g32p_row02_traceSegment_093_0000_0054, g32p_row02_traceSegment_093_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 108 13 14, g32p_row02_traceSegment_093_0108_0013, g32p_row02_traceSegment_093_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 135 13 14, g32p_row02_traceSegment_093_0135_0013, g32p_row02_traceSegment_093_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 108 27 27, g32p_row02_traceSegment_093_0108_0027, g32p_row02_traceSegment_093_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 162 13 14, g32p_row02_traceSegment_093_0162_0013, g32p_row02_traceSegment_093_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 202 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 189 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 189 13 14, g32p_row02_traceSegment_093_0189_0013, g32p_row02_traceSegment_093_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 162 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 162 27 27, g32p_row02_traceSegment_093_0162_0027, g32p_row02_traceSegment_093_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 108 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 108 54 54, g32p_row02_traceSegment_093_0108_0054, g32p_row02_traceSegment_093_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 0 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 108 108, g32p_row02_traceSegment_093_0000_0108, g32p_row02_traceSegment_093_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 229 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 216 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 216 13 14, g32p_row02_traceSegment_093_0216_0013, g32p_row02_traceSegment_093_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 256 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 243 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 243 13 14, g32p_row02_traceSegment_093_0243_0013, g32p_row02_traceSegment_093_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 216 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 216 27 27, g32p_row02_traceSegment_093_0216_0027, g32p_row02_traceSegment_093_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 270 13 14, g32p_row02_traceSegment_093_0270_0013, g32p_row02_traceSegment_093_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 297 13 14, g32p_row02_traceSegment_093_0297_0013, g32p_row02_traceSegment_093_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 270 27 27, g32p_row02_traceSegment_093_0270_0027, g32p_row02_traceSegment_093_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 216 54 54, g32p_row02_traceSegment_093_0216_0054, g32p_row02_traceSegment_093_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 324 13 14, g32p_row02_traceSegment_093_0324_0013, g32p_row02_traceSegment_093_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 351 13 14, g32p_row02_traceSegment_093_0351_0013, g32p_row02_traceSegment_093_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 324 27 27, g32p_row02_traceSegment_093_0324_0027, g32p_row02_traceSegment_093_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 378 13 14, g32p_row02_traceSegment_093_0378_0013, g32p_row02_traceSegment_093_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 405 13 14, g32p_row02_traceSegment_093_0405_0013, g32p_row02_traceSegment_093_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 378 27 27, g32p_row02_traceSegment_093_0378_0027, g32p_row02_traceSegment_093_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 324 54 54, g32p_row02_traceSegment_093_0324_0054, g32p_row02_traceSegment_093_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 216 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 216 108 108, g32p_row02_traceSegment_093_0216_0108, g32p_row02_traceSegment_093_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 0 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 216 216, g32p_row02_traceSegment_093_0000_0216, g32p_row02_traceSegment_093_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 432 13 14, g32p_row02_traceSegment_093_0432_0013, g32p_row02_traceSegment_093_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 459 13 14, g32p_row02_traceSegment_093_0459_0013, g32p_row02_traceSegment_093_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 432 27 27, g32p_row02_traceSegment_093_0432_0027, g32p_row02_traceSegment_093_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 486 13 14, g32p_row02_traceSegment_093_0486_0013, g32p_row02_traceSegment_093_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 513 13 14, g32p_row02_traceSegment_093_0513_0013, g32p_row02_traceSegment_093_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 486 27 27, g32p_row02_traceSegment_093_0486_0027, g32p_row02_traceSegment_093_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 432 54 54, g32p_row02_traceSegment_093_0432_0054, g32p_row02_traceSegment_093_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 540 13 14, g32p_row02_traceSegment_093_0540_0013, g32p_row02_traceSegment_093_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 567 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 567 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 567 13 14, g32p_row02_traceSegment_093_0567_0013, g32p_row02_traceSegment_093_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 540 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 540 27 27, g32p_row02_traceSegment_093_0540_0027, g32p_row02_traceSegment_093_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 594 13 14, g32p_row02_traceSegment_093_0594_0013, g32p_row02_traceSegment_093_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 621 13 14, g32p_row02_traceSegment_093_0621_0013, g32p_row02_traceSegment_093_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 594 27 27, g32p_row02_traceSegment_093_0594_0027, g32p_row02_traceSegment_093_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 540 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 540 54 54, g32p_row02_traceSegment_093_0540_0054, g32p_row02_traceSegment_093_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 432 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 432 108 108, g32p_row02_traceSegment_093_0432_0108, g32p_row02_traceSegment_093_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 648 13 14, g32p_row02_traceSegment_093_0648_0013, g32p_row02_traceSegment_093_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 675 13 14, g32p_row02_traceSegment_093_0675_0013, g32p_row02_traceSegment_093_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 648 27 27, g32p_row02_traceSegment_093_0648_0027, g32p_row02_traceSegment_093_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 702 13 14, g32p_row02_traceSegment_093_0702_0013, g32p_row02_traceSegment_093_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 729 13 14, g32p_row02_traceSegment_093_0729_0013, g32p_row02_traceSegment_093_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 702 27 27, g32p_row02_traceSegment_093_0702_0027, g32p_row02_traceSegment_093_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 648 54 54, g32p_row02_traceSegment_093_0648_0054, g32p_row02_traceSegment_093_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 756 13 14, g32p_row02_traceSegment_093_0756_0013, g32p_row02_traceSegment_093_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 796 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 783 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 783 13 14, g32p_row02_traceSegment_093_0783_0013, g32p_row02_traceSegment_093_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 756 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 756 27 27, g32p_row02_traceSegment_093_0756_0027, g32p_row02_traceSegment_093_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 810 13 14, g32p_row02_traceSegment_093_0810_0013, g32p_row02_traceSegment_093_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 837 13 14, g32p_row02_traceSegment_093_0837_0013, g32p_row02_traceSegment_093_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 810 27 27, g32p_row02_traceSegment_093_0810_0027, g32p_row02_traceSegment_093_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 756 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 756 54 54, g32p_row02_traceSegment_093_0756_0054, g32p_row02_traceSegment_093_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 648 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 648 108 108, g32p_row02_traceSegment_093_0648_0108, g32p_row02_traceSegment_093_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 432 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 432 216 216, g32p_row02_traceSegment_093_0432_0216, g32p_row02_traceSegment_093_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_093 0 864 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 432 432, g32p_row02_traceSegment_093_0000_0432, g32p_row02_traceSegment_093_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 864 13 14, g32p_row02_traceSegment_093_0864_0013, g32p_row02_traceSegment_093_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 891 13 14, g32p_row02_traceSegment_093_0891_0013, g32p_row02_traceSegment_093_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 864 27 27, g32p_row02_traceSegment_093_0864_0027, g32p_row02_traceSegment_093_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 918 13 14, g32p_row02_traceSegment_093_0918_0013, g32p_row02_traceSegment_093_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 945 13 14, g32p_row02_traceSegment_093_0945_0013, g32p_row02_traceSegment_093_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 918 27 27, g32p_row02_traceSegment_093_0918_0027, g32p_row02_traceSegment_093_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 864 54 54, g32p_row02_traceSegment_093_0864_0054, g32p_row02_traceSegment_093_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 972 13 14, g32p_row02_traceSegment_093_0972_0013, g32p_row02_traceSegment_093_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 999 13 14, g32p_row02_traceSegment_093_0999_0013, g32p_row02_traceSegment_093_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 972 27 27, g32p_row02_traceSegment_093_0972_0027, g32p_row02_traceSegment_093_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1026 13 14, g32p_row02_traceSegment_093_1026_0013, g32p_row02_traceSegment_093_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1053 13 14, g32p_row02_traceSegment_093_1053_0013, g32p_row02_traceSegment_093_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1026 27 27, g32p_row02_traceSegment_093_1026_0027, g32p_row02_traceSegment_093_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 972 54 54, g32p_row02_traceSegment_093_0972_0054, g32p_row02_traceSegment_093_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 864 108 108, g32p_row02_traceSegment_093_0864_0108, g32p_row02_traceSegment_093_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1080 13 14, g32p_row02_traceSegment_093_1080_0013, g32p_row02_traceSegment_093_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1107 13 14, g32p_row02_traceSegment_093_1107_0013, g32p_row02_traceSegment_093_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1080 27 27, g32p_row02_traceSegment_093_1080_0027, g32p_row02_traceSegment_093_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1134 13 14, g32p_row02_traceSegment_093_1134_0013, g32p_row02_traceSegment_093_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1161 13 14, g32p_row02_traceSegment_093_1161_0013, g32p_row02_traceSegment_093_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1134 27 27, g32p_row02_traceSegment_093_1134_0027, g32p_row02_traceSegment_093_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1080 54 54, g32p_row02_traceSegment_093_1080_0054, g32p_row02_traceSegment_093_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1188 13 14, g32p_row02_traceSegment_093_1188_0013, g32p_row02_traceSegment_093_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1215 13 14, g32p_row02_traceSegment_093_1215_0013, g32p_row02_traceSegment_093_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1188 27 27, g32p_row02_traceSegment_093_1188_0027, g32p_row02_traceSegment_093_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1242 13 14, g32p_row02_traceSegment_093_1242_0013, g32p_row02_traceSegment_093_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1269 13 14, g32p_row02_traceSegment_093_1269_0013, g32p_row02_traceSegment_093_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1242 27 27, g32p_row02_traceSegment_093_1242_0027, g32p_row02_traceSegment_093_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1188 54 54, g32p_row02_traceSegment_093_1188_0054, g32p_row02_traceSegment_093_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1080 108 108, g32p_row02_traceSegment_093_1080_0108, g32p_row02_traceSegment_093_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 864 216 216, g32p_row02_traceSegment_093_0864_0216, g32p_row02_traceSegment_093_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1296 13 14, g32p_row02_traceSegment_093_1296_0013, g32p_row02_traceSegment_093_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1323 13 14, g32p_row02_traceSegment_093_1323_0013, g32p_row02_traceSegment_093_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1296 27 27, g32p_row02_traceSegment_093_1296_0027, g32p_row02_traceSegment_093_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1350 13 14, g32p_row02_traceSegment_093_1350_0013, g32p_row02_traceSegment_093_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1377 13 14, g32p_row02_traceSegment_093_1377_0013, g32p_row02_traceSegment_093_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1350 27 27, g32p_row02_traceSegment_093_1350_0027, g32p_row02_traceSegment_093_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1296 54 54, g32p_row02_traceSegment_093_1296_0054, g32p_row02_traceSegment_093_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1404 13 14, g32p_row02_traceSegment_093_1404_0013, g32p_row02_traceSegment_093_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1431 13 14, g32p_row02_traceSegment_093_1431_0013, g32p_row02_traceSegment_093_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1404 27 27, g32p_row02_traceSegment_093_1404_0027, g32p_row02_traceSegment_093_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1458 13 14, g32p_row02_traceSegment_093_1458_0013, g32p_row02_traceSegment_093_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1485 13 14, g32p_row02_traceSegment_093_1485_0013, g32p_row02_traceSegment_093_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1458 27 27, g32p_row02_traceSegment_093_1458_0027, g32p_row02_traceSegment_093_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1404 54 54, g32p_row02_traceSegment_093_1404_0054, g32p_row02_traceSegment_093_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1296 108 108, g32p_row02_traceSegment_093_1296_0108, g32p_row02_traceSegment_093_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1512 13 14, g32p_row02_traceSegment_093_1512_0013, g32p_row02_traceSegment_093_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1539 13 14, g32p_row02_traceSegment_093_1539_0013, g32p_row02_traceSegment_093_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1512 27 27, g32p_row02_traceSegment_093_1512_0027, g32p_row02_traceSegment_093_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1566 13 14, g32p_row02_traceSegment_093_1566_0013, g32p_row02_traceSegment_093_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1593 13 14, g32p_row02_traceSegment_093_1593_0013, g32p_row02_traceSegment_093_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1566 27 27, g32p_row02_traceSegment_093_1566_0027, g32p_row02_traceSegment_093_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1512 54 54, g32p_row02_traceSegment_093_1512_0054, g32p_row02_traceSegment_093_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1620 13 14, g32p_row02_traceSegment_093_1620_0013, g32p_row02_traceSegment_093_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1647 13 14, g32p_row02_traceSegment_093_1647_0013, g32p_row02_traceSegment_093_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1620 27 27, g32p_row02_traceSegment_093_1620_0027, g32p_row02_traceSegment_093_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1674 13 14, g32p_row02_traceSegment_093_1674_0013, g32p_row02_traceSegment_093_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1701 13 14, g32p_row02_traceSegment_093_1701_0013, g32p_row02_traceSegment_093_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1674 27 27, g32p_row02_traceSegment_093_1674_0027, g32p_row02_traceSegment_093_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1620 54 54, g32p_row02_traceSegment_093_1620_0054, g32p_row02_traceSegment_093_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1512 108 108, g32p_row02_traceSegment_093_1512_0108, g32p_row02_traceSegment_093_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1296 216 216, g32p_row02_traceSegment_093_1296_0216, g32p_row02_traceSegment_093_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_093 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 864 432 432, g32p_row02_traceSegment_093_0864_0432, g32p_row02_traceSegment_093_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_093 0 1728 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 864 864, g32p_row02_traceSegment_093_0000_0864, g32p_row02_traceSegment_093_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1728 13 14, g32p_row02_traceSegment_093_1728_0013, g32p_row02_traceSegment_093_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1755 13 14, g32p_row02_traceSegment_093_1755_0013, g32p_row02_traceSegment_093_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1728 27 27, g32p_row02_traceSegment_093_1728_0027, g32p_row02_traceSegment_093_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1782 13 14, g32p_row02_traceSegment_093_1782_0013, g32p_row02_traceSegment_093_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1809 13 14, g32p_row02_traceSegment_093_1809_0013, g32p_row02_traceSegment_093_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1782 27 27, g32p_row02_traceSegment_093_1782_0027, g32p_row02_traceSegment_093_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1728 54 54, g32p_row02_traceSegment_093_1728_0054, g32p_row02_traceSegment_093_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1836 13 14, g32p_row02_traceSegment_093_1836_0013, g32p_row02_traceSegment_093_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1863 13 14, g32p_row02_traceSegment_093_1863_0013, g32p_row02_traceSegment_093_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1836 27 27, g32p_row02_traceSegment_093_1836_0027, g32p_row02_traceSegment_093_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1890 13 14, g32p_row02_traceSegment_093_1890_0013, g32p_row02_traceSegment_093_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1917 13 14, g32p_row02_traceSegment_093_1917_0013, g32p_row02_traceSegment_093_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1890 27 27, g32p_row02_traceSegment_093_1890_0027, g32p_row02_traceSegment_093_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1836 54 54, g32p_row02_traceSegment_093_1836_0054, g32p_row02_traceSegment_093_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1728 108 108, g32p_row02_traceSegment_093_1728_0108, g32p_row02_traceSegment_093_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1944 13 14, g32p_row02_traceSegment_093_1944_0013, g32p_row02_traceSegment_093_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1971 13 14, g32p_row02_traceSegment_093_1971_0013, g32p_row02_traceSegment_093_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1944 27 27, g32p_row02_traceSegment_093_1944_0027, g32p_row02_traceSegment_093_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2011 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 1998 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1998 13 14, g32p_row02_traceSegment_093_1998_0013, g32p_row02_traceSegment_093_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2038 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2025 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2025 13 14, g32p_row02_traceSegment_093_2025_0013, g32p_row02_traceSegment_093_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 1998 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1998 27 27, g32p_row02_traceSegment_093_1998_0027, g32p_row02_traceSegment_093_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 1944 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1944 54 54, g32p_row02_traceSegment_093_1944_0054, g32p_row02_traceSegment_093_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2052 13 14, g32p_row02_traceSegment_093_2052_0013, g32p_row02_traceSegment_093_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2079 13 14, g32p_row02_traceSegment_093_2079_0013, g32p_row02_traceSegment_093_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2052 27 27, g32p_row02_traceSegment_093_2052_0027, g32p_row02_traceSegment_093_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2106 13 14, g32p_row02_traceSegment_093_2106_0013, g32p_row02_traceSegment_093_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2133 13 14, g32p_row02_traceSegment_093_2133_0013, g32p_row02_traceSegment_093_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2106 27 27, g32p_row02_traceSegment_093_2106_0027, g32p_row02_traceSegment_093_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2052 54 54, g32p_row02_traceSegment_093_2052_0054, g32p_row02_traceSegment_093_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 1944 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1944 108 108, g32p_row02_traceSegment_093_1944_0108, g32p_row02_traceSegment_093_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1728 216 216, g32p_row02_traceSegment_093_1728_0216, g32p_row02_traceSegment_093_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2160 13 14, g32p_row02_traceSegment_093_2160_0013, g32p_row02_traceSegment_093_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2187 13 14, g32p_row02_traceSegment_093_2187_0013, g32p_row02_traceSegment_093_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2160 27 27, g32p_row02_traceSegment_093_2160_0027, g32p_row02_traceSegment_093_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2214 13 14, g32p_row02_traceSegment_093_2214_0013, g32p_row02_traceSegment_093_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2241 13 14, g32p_row02_traceSegment_093_2241_0013, g32p_row02_traceSegment_093_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2214 27 27, g32p_row02_traceSegment_093_2214_0027, g32p_row02_traceSegment_093_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2160 54 54, g32p_row02_traceSegment_093_2160_0054, g32p_row02_traceSegment_093_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2268 13 14, g32p_row02_traceSegment_093_2268_0013, g32p_row02_traceSegment_093_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2295 13 14, g32p_row02_traceSegment_093_2295_0013, g32p_row02_traceSegment_093_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2268 27 27, g32p_row02_traceSegment_093_2268_0027, g32p_row02_traceSegment_093_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2322 13 14, g32p_row02_traceSegment_093_2322_0013, g32p_row02_traceSegment_093_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2349 13 14, g32p_row02_traceSegment_093_2349_0013, g32p_row02_traceSegment_093_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2322 27 27, g32p_row02_traceSegment_093_2322_0027, g32p_row02_traceSegment_093_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2268 54 54, g32p_row02_traceSegment_093_2268_0054, g32p_row02_traceSegment_093_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2160 108 108, g32p_row02_traceSegment_093_2160_0108, g32p_row02_traceSegment_093_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2376 13 14, g32p_row02_traceSegment_093_2376_0013, g32p_row02_traceSegment_093_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2403 13 14, g32p_row02_traceSegment_093_2403_0013, g32p_row02_traceSegment_093_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2376 27 27, g32p_row02_traceSegment_093_2376_0027, g32p_row02_traceSegment_093_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2430 13 14, g32p_row02_traceSegment_093_2430_0013, g32p_row02_traceSegment_093_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2457 13 14, g32p_row02_traceSegment_093_2457_0013, g32p_row02_traceSegment_093_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2430 27 27, g32p_row02_traceSegment_093_2430_0027, g32p_row02_traceSegment_093_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2376 54 54, g32p_row02_traceSegment_093_2376_0054, g32p_row02_traceSegment_093_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2484 13 14, g32p_row02_traceSegment_093_2484_0013, g32p_row02_traceSegment_093_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2511 13 14, g32p_row02_traceSegment_093_2511_0013, g32p_row02_traceSegment_093_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2484 27 27, g32p_row02_traceSegment_093_2484_0027, g32p_row02_traceSegment_093_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2538 13 14, g32p_row02_traceSegment_093_2538_0013, g32p_row02_traceSegment_093_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2565 13 14, g32p_row02_traceSegment_093_2565_0013, g32p_row02_traceSegment_093_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2538 27 27, g32p_row02_traceSegment_093_2538_0027, g32p_row02_traceSegment_093_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2484 54 54, g32p_row02_traceSegment_093_2484_0054, g32p_row02_traceSegment_093_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2376 108 108, g32p_row02_traceSegment_093_2376_0108, g32p_row02_traceSegment_093_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2160 216 216, g32p_row02_traceSegment_093_2160_0216, g32p_row02_traceSegment_093_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1728 432 432, g32p_row02_traceSegment_093_1728_0432, g32p_row02_traceSegment_093_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2592 13 14, g32p_row02_traceSegment_093_2592_0013, g32p_row02_traceSegment_093_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2619 13 14, g32p_row02_traceSegment_093_2619_0013, g32p_row02_traceSegment_093_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2592 27 27, g32p_row02_traceSegment_093_2592_0027, g32p_row02_traceSegment_093_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2646 13 14, g32p_row02_traceSegment_093_2646_0013, g32p_row02_traceSegment_093_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2673 13 14, g32p_row02_traceSegment_093_2673_0013, g32p_row02_traceSegment_093_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2646 27 27, g32p_row02_traceSegment_093_2646_0027, g32p_row02_traceSegment_093_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2592 54 54, g32p_row02_traceSegment_093_2592_0054, g32p_row02_traceSegment_093_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2700 13 14, g32p_row02_traceSegment_093_2700_0013, g32p_row02_traceSegment_093_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2727 13 14, g32p_row02_traceSegment_093_2727_0013, g32p_row02_traceSegment_093_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2700 27 27, g32p_row02_traceSegment_093_2700_0027, g32p_row02_traceSegment_093_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2754 13 14, g32p_row02_traceSegment_093_2754_0013, g32p_row02_traceSegment_093_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2781 13 14, g32p_row02_traceSegment_093_2781_0013, g32p_row02_traceSegment_093_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2754 27 27, g32p_row02_traceSegment_093_2754_0027, g32p_row02_traceSegment_093_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2700 54 54, g32p_row02_traceSegment_093_2700_0054, g32p_row02_traceSegment_093_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2592 108 108, g32p_row02_traceSegment_093_2592_0108, g32p_row02_traceSegment_093_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2808 13 14, g32p_row02_traceSegment_093_2808_0013, g32p_row02_traceSegment_093_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2835 13 14, g32p_row02_traceSegment_093_2835_0013, g32p_row02_traceSegment_093_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2808 27 27, g32p_row02_traceSegment_093_2808_0027, g32p_row02_traceSegment_093_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2862 13 14, g32p_row02_traceSegment_093_2862_0013, g32p_row02_traceSegment_093_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2889 13 14, g32p_row02_traceSegment_093_2889_0013, g32p_row02_traceSegment_093_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2862 27 27, g32p_row02_traceSegment_093_2862_0027, g32p_row02_traceSegment_093_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2808 54 54, g32p_row02_traceSegment_093_2808_0054, g32p_row02_traceSegment_093_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2916 13 14, g32p_row02_traceSegment_093_2916_0013, g32p_row02_traceSegment_093_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2943 13 14, g32p_row02_traceSegment_093_2943_0013, g32p_row02_traceSegment_093_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2916 27 27, g32p_row02_traceSegment_093_2916_0027, g32p_row02_traceSegment_093_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2970 13 14, g32p_row02_traceSegment_093_2970_0013, g32p_row02_traceSegment_093_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2997 13 14, g32p_row02_traceSegment_093_2997_0013, g32p_row02_traceSegment_093_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2970 27 27, g32p_row02_traceSegment_093_2970_0027, g32p_row02_traceSegment_093_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2916 54 54, g32p_row02_traceSegment_093_2916_0054, g32p_row02_traceSegment_093_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2808 108 108, g32p_row02_traceSegment_093_2808_0108, g32p_row02_traceSegment_093_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2592 216 216, g32p_row02_traceSegment_093_2592_0216, g32p_row02_traceSegment_093_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3024 13 14, g32p_row02_traceSegment_093_3024_0013, g32p_row02_traceSegment_093_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3051 13 14, g32p_row02_traceSegment_093_3051_0013, g32p_row02_traceSegment_093_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3024 27 27, g32p_row02_traceSegment_093_3024_0027, g32p_row02_traceSegment_093_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3078 13 14, g32p_row02_traceSegment_093_3078_0013, g32p_row02_traceSegment_093_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3105 13 14, g32p_row02_traceSegment_093_3105_0013, g32p_row02_traceSegment_093_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3078 27 27, g32p_row02_traceSegment_093_3078_0027, g32p_row02_traceSegment_093_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3024 54 54, g32p_row02_traceSegment_093_3024_0054, g32p_row02_traceSegment_093_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3132 13 14, g32p_row02_traceSegment_093_3132_0013, g32p_row02_traceSegment_093_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3159 13 14, g32p_row02_traceSegment_093_3159_0013, g32p_row02_traceSegment_093_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3132 27 27, g32p_row02_traceSegment_093_3132_0027, g32p_row02_traceSegment_093_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3186 13 14, g32p_row02_traceSegment_093_3186_0013, g32p_row02_traceSegment_093_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3213 13 14, g32p_row02_traceSegment_093_3213_0013, g32p_row02_traceSegment_093_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3186 27 27, g32p_row02_traceSegment_093_3186_0027, g32p_row02_traceSegment_093_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3132 54 54, g32p_row02_traceSegment_093_3132_0054, g32p_row02_traceSegment_093_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3024 108 108, g32p_row02_traceSegment_093_3024_0108, g32p_row02_traceSegment_093_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3240 13 14, g32p_row02_traceSegment_093_3240_0013, g32p_row02_traceSegment_093_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3267 13 14, g32p_row02_traceSegment_093_3267_0013, g32p_row02_traceSegment_093_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3240 27 27, g32p_row02_traceSegment_093_3240_0027, g32p_row02_traceSegment_093_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3294 13 14, g32p_row02_traceSegment_093_3294_0013, g32p_row02_traceSegment_093_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3321 13 14, g32p_row02_traceSegment_093_3321_0013, g32p_row02_traceSegment_093_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3294 27 27, g32p_row02_traceSegment_093_3294_0027, g32p_row02_traceSegment_093_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3240 54 54, g32p_row02_traceSegment_093_3240_0054, g32p_row02_traceSegment_093_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3348 13 14, g32p_row02_traceSegment_093_3348_0013, g32p_row02_traceSegment_093_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3375 13 14, g32p_row02_traceSegment_093_3375_0013, g32p_row02_traceSegment_093_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3348 27 27, g32p_row02_traceSegment_093_3348_0027, g32p_row02_traceSegment_093_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3402 13 14, g32p_row02_traceSegment_093_3402_0013, g32p_row02_traceSegment_093_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_093 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_093 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_093_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_093 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3429 13 14, g32p_row02_traceSegment_093_3429_0013, g32p_row02_traceSegment_093_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_093 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3402 27 27, g32p_row02_traceSegment_093_3402_0027, g32p_row02_traceSegment_093_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_093 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3348 54 54, g32p_row02_traceSegment_093_3348_0054, g32p_row02_traceSegment_093_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_093 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3240 108 108, g32p_row02_traceSegment_093_3240_0108, g32p_row02_traceSegment_093_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_093_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_093 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 3024 216 216, g32p_row02_traceSegment_093_3024_0216, g32p_row02_traceSegment_093_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_093_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_093 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 2592 432 432, g32p_row02_traceSegment_093_2592_0432, g32p_row02_traceSegment_093_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_093_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_093 1728 1728 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 1728 864 864, g32p_row02_traceSegment_093_1728_0864, g32p_row02_traceSegment_093_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_093_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_093 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_093 0 1728 1728, g32p_row02_traceSegment_093_0000_1728, g32p_row02_traceSegment_093_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 93 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_093_0000_3456

end HodgeLean.Foundations.Program

end
end
