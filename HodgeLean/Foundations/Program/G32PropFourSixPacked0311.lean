import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0310

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_094 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 94 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_094_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 13 14, g32p_row02_traceSegment_094_0000_0013, g32p_row02_traceSegment_094_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 27 13 14, g32p_row02_traceSegment_094_0027_0013, g32p_row02_traceSegment_094_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 27 27, g32p_row02_traceSegment_094_0000_0027, g32p_row02_traceSegment_094_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 54 13 14, g32p_row02_traceSegment_094_0054_0013, g32p_row02_traceSegment_094_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 81 13 14, g32p_row02_traceSegment_094_0081_0013, g32p_row02_traceSegment_094_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 54 27 27, g32p_row02_traceSegment_094_0054_0027, g32p_row02_traceSegment_094_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 54 54, g32p_row02_traceSegment_094_0000_0054, g32p_row02_traceSegment_094_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 108 13 14, g32p_row02_traceSegment_094_0108_0013, g32p_row02_traceSegment_094_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 135 13 14, g32p_row02_traceSegment_094_0135_0013, g32p_row02_traceSegment_094_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 108 27 27, g32p_row02_traceSegment_094_0108_0027, g32p_row02_traceSegment_094_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 162 13 14, g32p_row02_traceSegment_094_0162_0013, g32p_row02_traceSegment_094_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 189 13 14, g32p_row02_traceSegment_094_0189_0013, g32p_row02_traceSegment_094_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 162 27 27, g32p_row02_traceSegment_094_0162_0027, g32p_row02_traceSegment_094_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 108 54 54, g32p_row02_traceSegment_094_0108_0054, g32p_row02_traceSegment_094_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 108 108, g32p_row02_traceSegment_094_0000_0108, g32p_row02_traceSegment_094_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 216 13 14, g32p_row02_traceSegment_094_0216_0013, g32p_row02_traceSegment_094_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 243 13 14, g32p_row02_traceSegment_094_0243_0013, g32p_row02_traceSegment_094_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 216 27 27, g32p_row02_traceSegment_094_0216_0027, g32p_row02_traceSegment_094_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 270 13 14, g32p_row02_traceSegment_094_0270_0013, g32p_row02_traceSegment_094_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 297 13 14, g32p_row02_traceSegment_094_0297_0013, g32p_row02_traceSegment_094_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 270 27 27, g32p_row02_traceSegment_094_0270_0027, g32p_row02_traceSegment_094_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 216 54 54, g32p_row02_traceSegment_094_0216_0054, g32p_row02_traceSegment_094_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 324 13 14, g32p_row02_traceSegment_094_0324_0013, g32p_row02_traceSegment_094_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 351 13 14, g32p_row02_traceSegment_094_0351_0013, g32p_row02_traceSegment_094_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 324 27 27, g32p_row02_traceSegment_094_0324_0027, g32p_row02_traceSegment_094_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 378 13 14, g32p_row02_traceSegment_094_0378_0013, g32p_row02_traceSegment_094_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 405 13 14, g32p_row02_traceSegment_094_0405_0013, g32p_row02_traceSegment_094_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 378 27 27, g32p_row02_traceSegment_094_0378_0027, g32p_row02_traceSegment_094_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 324 54 54, g32p_row02_traceSegment_094_0324_0054, g32p_row02_traceSegment_094_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 216 108 108, g32p_row02_traceSegment_094_0216_0108, g32p_row02_traceSegment_094_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 216 216, g32p_row02_traceSegment_094_0000_0216, g32p_row02_traceSegment_094_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 432 13 14, g32p_row02_traceSegment_094_0432_0013, g32p_row02_traceSegment_094_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 459 13 14, g32p_row02_traceSegment_094_0459_0013, g32p_row02_traceSegment_094_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 432 27 27, g32p_row02_traceSegment_094_0432_0027, g32p_row02_traceSegment_094_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 486 13 14, g32p_row02_traceSegment_094_0486_0013, g32p_row02_traceSegment_094_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 513 13 14, g32p_row02_traceSegment_094_0513_0013, g32p_row02_traceSegment_094_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 486 27 27, g32p_row02_traceSegment_094_0486_0027, g32p_row02_traceSegment_094_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 432 54 54, g32p_row02_traceSegment_094_0432_0054, g32p_row02_traceSegment_094_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 540 13 14, g32p_row02_traceSegment_094_0540_0013, g32p_row02_traceSegment_094_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 567 13 14, g32p_row02_traceSegment_094_0567_0013, g32p_row02_traceSegment_094_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 540 27 27, g32p_row02_traceSegment_094_0540_0027, g32p_row02_traceSegment_094_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 594 13 14, g32p_row02_traceSegment_094_0594_0013, g32p_row02_traceSegment_094_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 621 13 14, g32p_row02_traceSegment_094_0621_0013, g32p_row02_traceSegment_094_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 594 27 27, g32p_row02_traceSegment_094_0594_0027, g32p_row02_traceSegment_094_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 540 54 54, g32p_row02_traceSegment_094_0540_0054, g32p_row02_traceSegment_094_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 432 108 108, g32p_row02_traceSegment_094_0432_0108, g32p_row02_traceSegment_094_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 648 13 14, g32p_row02_traceSegment_094_0648_0013, g32p_row02_traceSegment_094_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 675 13 14, g32p_row02_traceSegment_094_0675_0013, g32p_row02_traceSegment_094_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 648 27 27, g32p_row02_traceSegment_094_0648_0027, g32p_row02_traceSegment_094_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 702 13 14, g32p_row02_traceSegment_094_0702_0013, g32p_row02_traceSegment_094_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 729 13 14, g32p_row02_traceSegment_094_0729_0013, g32p_row02_traceSegment_094_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 702 27 27, g32p_row02_traceSegment_094_0702_0027, g32p_row02_traceSegment_094_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 648 54 54, g32p_row02_traceSegment_094_0648_0054, g32p_row02_traceSegment_094_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 756 13 14, g32p_row02_traceSegment_094_0756_0013, g32p_row02_traceSegment_094_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 783 13 14, g32p_row02_traceSegment_094_0783_0013, g32p_row02_traceSegment_094_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 756 27 27, g32p_row02_traceSegment_094_0756_0027, g32p_row02_traceSegment_094_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 810 13 14, g32p_row02_traceSegment_094_0810_0013, g32p_row02_traceSegment_094_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 837 13 14, g32p_row02_traceSegment_094_0837_0013, g32p_row02_traceSegment_094_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 810 27 27, g32p_row02_traceSegment_094_0810_0027, g32p_row02_traceSegment_094_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 756 54 54, g32p_row02_traceSegment_094_0756_0054, g32p_row02_traceSegment_094_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 648 108 108, g32p_row02_traceSegment_094_0648_0108, g32p_row02_traceSegment_094_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 432 216 216, g32p_row02_traceSegment_094_0432_0216, g32p_row02_traceSegment_094_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_094 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 432 432, g32p_row02_traceSegment_094_0000_0432, g32p_row02_traceSegment_094_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 864 13 14, g32p_row02_traceSegment_094_0864_0013, g32p_row02_traceSegment_094_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 891 13 14, g32p_row02_traceSegment_094_0891_0013, g32p_row02_traceSegment_094_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 864 27 27, g32p_row02_traceSegment_094_0864_0027, g32p_row02_traceSegment_094_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 918 13 14, g32p_row02_traceSegment_094_0918_0013, g32p_row02_traceSegment_094_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 945 13 14, g32p_row02_traceSegment_094_0945_0013, g32p_row02_traceSegment_094_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 918 27 27, g32p_row02_traceSegment_094_0918_0027, g32p_row02_traceSegment_094_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 864 54 54, g32p_row02_traceSegment_094_0864_0054, g32p_row02_traceSegment_094_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 972 13 14, g32p_row02_traceSegment_094_0972_0013, g32p_row02_traceSegment_094_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 999 13 14, g32p_row02_traceSegment_094_0999_0013, g32p_row02_traceSegment_094_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 972 27 27, g32p_row02_traceSegment_094_0972_0027, g32p_row02_traceSegment_094_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1026 13 14, g32p_row02_traceSegment_094_1026_0013, g32p_row02_traceSegment_094_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1053 13 14, g32p_row02_traceSegment_094_1053_0013, g32p_row02_traceSegment_094_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1026 27 27, g32p_row02_traceSegment_094_1026_0027, g32p_row02_traceSegment_094_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 972 54 54, g32p_row02_traceSegment_094_0972_0054, g32p_row02_traceSegment_094_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 864 108 108, g32p_row02_traceSegment_094_0864_0108, g32p_row02_traceSegment_094_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1080 13 14, g32p_row02_traceSegment_094_1080_0013, g32p_row02_traceSegment_094_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1107 13 14, g32p_row02_traceSegment_094_1107_0013, g32p_row02_traceSegment_094_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1080 27 27, g32p_row02_traceSegment_094_1080_0027, g32p_row02_traceSegment_094_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1134 13 14, g32p_row02_traceSegment_094_1134_0013, g32p_row02_traceSegment_094_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1161 13 14, g32p_row02_traceSegment_094_1161_0013, g32p_row02_traceSegment_094_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1134 27 27, g32p_row02_traceSegment_094_1134_0027, g32p_row02_traceSegment_094_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1080 54 54, g32p_row02_traceSegment_094_1080_0054, g32p_row02_traceSegment_094_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1188 13 14, g32p_row02_traceSegment_094_1188_0013, g32p_row02_traceSegment_094_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1215 13 14, g32p_row02_traceSegment_094_1215_0013, g32p_row02_traceSegment_094_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1188 27 27, g32p_row02_traceSegment_094_1188_0027, g32p_row02_traceSegment_094_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1242 13 14, g32p_row02_traceSegment_094_1242_0013, g32p_row02_traceSegment_094_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1269 13 14, g32p_row02_traceSegment_094_1269_0013, g32p_row02_traceSegment_094_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1242 27 27, g32p_row02_traceSegment_094_1242_0027, g32p_row02_traceSegment_094_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1188 54 54, g32p_row02_traceSegment_094_1188_0054, g32p_row02_traceSegment_094_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1080 108 108, g32p_row02_traceSegment_094_1080_0108, g32p_row02_traceSegment_094_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 864 216 216, g32p_row02_traceSegment_094_0864_0216, g32p_row02_traceSegment_094_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1296 13 14, g32p_row02_traceSegment_094_1296_0013, g32p_row02_traceSegment_094_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1323 13 14, g32p_row02_traceSegment_094_1323_0013, g32p_row02_traceSegment_094_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1296 27 27, g32p_row02_traceSegment_094_1296_0027, g32p_row02_traceSegment_094_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1350 13 14, g32p_row02_traceSegment_094_1350_0013, g32p_row02_traceSegment_094_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1377 13 14, g32p_row02_traceSegment_094_1377_0013, g32p_row02_traceSegment_094_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1350 27 27, g32p_row02_traceSegment_094_1350_0027, g32p_row02_traceSegment_094_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1296 54 54, g32p_row02_traceSegment_094_1296_0054, g32p_row02_traceSegment_094_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1404 13 14, g32p_row02_traceSegment_094_1404_0013, g32p_row02_traceSegment_094_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1431 13 14, g32p_row02_traceSegment_094_1431_0013, g32p_row02_traceSegment_094_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1404 27 27, g32p_row02_traceSegment_094_1404_0027, g32p_row02_traceSegment_094_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1458 13 14, g32p_row02_traceSegment_094_1458_0013, g32p_row02_traceSegment_094_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1485 13 14, g32p_row02_traceSegment_094_1485_0013, g32p_row02_traceSegment_094_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1458 27 27, g32p_row02_traceSegment_094_1458_0027, g32p_row02_traceSegment_094_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1404 54 54, g32p_row02_traceSegment_094_1404_0054, g32p_row02_traceSegment_094_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1296 108 108, g32p_row02_traceSegment_094_1296_0108, g32p_row02_traceSegment_094_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1512 13 14, g32p_row02_traceSegment_094_1512_0013, g32p_row02_traceSegment_094_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1539 13 14, g32p_row02_traceSegment_094_1539_0013, g32p_row02_traceSegment_094_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1512 27 27, g32p_row02_traceSegment_094_1512_0027, g32p_row02_traceSegment_094_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1566 13 14, g32p_row02_traceSegment_094_1566_0013, g32p_row02_traceSegment_094_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1593 13 14, g32p_row02_traceSegment_094_1593_0013, g32p_row02_traceSegment_094_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1566 27 27, g32p_row02_traceSegment_094_1566_0027, g32p_row02_traceSegment_094_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1512 54 54, g32p_row02_traceSegment_094_1512_0054, g32p_row02_traceSegment_094_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1620 13 14, g32p_row02_traceSegment_094_1620_0013, g32p_row02_traceSegment_094_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1647 13 14, g32p_row02_traceSegment_094_1647_0013, g32p_row02_traceSegment_094_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1620 27 27, g32p_row02_traceSegment_094_1620_0027, g32p_row02_traceSegment_094_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1674 13 14, g32p_row02_traceSegment_094_1674_0013, g32p_row02_traceSegment_094_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1701 13 14, g32p_row02_traceSegment_094_1701_0013, g32p_row02_traceSegment_094_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1674 27 27, g32p_row02_traceSegment_094_1674_0027, g32p_row02_traceSegment_094_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1620 54 54, g32p_row02_traceSegment_094_1620_0054, g32p_row02_traceSegment_094_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1512 108 108, g32p_row02_traceSegment_094_1512_0108, g32p_row02_traceSegment_094_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1296 216 216, g32p_row02_traceSegment_094_1296_0216, g32p_row02_traceSegment_094_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_094 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 864 432 432, g32p_row02_traceSegment_094_0864_0432, g32p_row02_traceSegment_094_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_094 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 864 864, g32p_row02_traceSegment_094_0000_0864, g32p_row02_traceSegment_094_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1728 13 14, g32p_row02_traceSegment_094_1728_0013, g32p_row02_traceSegment_094_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1755 13 14, g32p_row02_traceSegment_094_1755_0013, g32p_row02_traceSegment_094_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1728 27 27, g32p_row02_traceSegment_094_1728_0027, g32p_row02_traceSegment_094_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1782 13 14, g32p_row02_traceSegment_094_1782_0013, g32p_row02_traceSegment_094_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1822 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1809 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1809 13 14, g32p_row02_traceSegment_094_1809_0013, g32p_row02_traceSegment_094_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1782 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1782 27 27, g32p_row02_traceSegment_094_1782_0027, g32p_row02_traceSegment_094_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1728 54 54, g32p_row02_traceSegment_094_1728_0054, g32p_row02_traceSegment_094_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1849 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1836 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1836 13 14, g32p_row02_traceSegment_094_1836_0013, g32p_row02_traceSegment_094_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1863 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1863 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1863 13 14, g32p_row02_traceSegment_094_1863_0013, g32p_row02_traceSegment_094_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1836 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1836 27 27, g32p_row02_traceSegment_094_1836_0027, g32p_row02_traceSegment_094_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1890 13 14, g32p_row02_traceSegment_094_1890_0013, g32p_row02_traceSegment_094_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1917 13 14, g32p_row02_traceSegment_094_1917_0013, g32p_row02_traceSegment_094_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1890 27 27, g32p_row02_traceSegment_094_1890_0027, g32p_row02_traceSegment_094_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1836 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1836 54 54, g32p_row02_traceSegment_094_1836_0054, g32p_row02_traceSegment_094_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1728 108 108, g32p_row02_traceSegment_094_1728_0108, g32p_row02_traceSegment_094_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1944 13 14, g32p_row02_traceSegment_094_1944_0013, g32p_row02_traceSegment_094_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1971 13 14, g32p_row02_traceSegment_094_1971_0013, g32p_row02_traceSegment_094_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1944 27 27, g32p_row02_traceSegment_094_1944_0027, g32p_row02_traceSegment_094_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1998 13 14, g32p_row02_traceSegment_094_1998_0013, g32p_row02_traceSegment_094_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2025 13 14, g32p_row02_traceSegment_094_2025_0013, g32p_row02_traceSegment_094_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1998 27 27, g32p_row02_traceSegment_094_1998_0027, g32p_row02_traceSegment_094_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1944 54 54, g32p_row02_traceSegment_094_1944_0054, g32p_row02_traceSegment_094_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2052 13 14, g32p_row02_traceSegment_094_2052_0013, g32p_row02_traceSegment_094_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2079 13 14, g32p_row02_traceSegment_094_2079_0013, g32p_row02_traceSegment_094_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2052 27 27, g32p_row02_traceSegment_094_2052_0027, g32p_row02_traceSegment_094_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2106 13 14, g32p_row02_traceSegment_094_2106_0013, g32p_row02_traceSegment_094_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2133 13 14, g32p_row02_traceSegment_094_2133_0013, g32p_row02_traceSegment_094_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2106 27 27, g32p_row02_traceSegment_094_2106_0027, g32p_row02_traceSegment_094_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2052 54 54, g32p_row02_traceSegment_094_2052_0054, g32p_row02_traceSegment_094_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1944 108 108, g32p_row02_traceSegment_094_1944_0108, g32p_row02_traceSegment_094_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1728 216 216, g32p_row02_traceSegment_094_1728_0216, g32p_row02_traceSegment_094_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2160 13 14, g32p_row02_traceSegment_094_2160_0013, g32p_row02_traceSegment_094_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2187 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2200 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2187 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2187 13 14, g32p_row02_traceSegment_094_2187_0013, g32p_row02_traceSegment_094_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2160 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2160 27 27, g32p_row02_traceSegment_094_2160_0027, g32p_row02_traceSegment_094_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2214 13 14, g32p_row02_traceSegment_094_2214_0013, g32p_row02_traceSegment_094_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2241 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2241 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2241 13 14, g32p_row02_traceSegment_094_2241_0013, g32p_row02_traceSegment_094_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2214 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2214 27 27, g32p_row02_traceSegment_094_2214_0027, g32p_row02_traceSegment_094_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2160 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2160 54 54, g32p_row02_traceSegment_094_2160_0054, g32p_row02_traceSegment_094_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2268 13 14, g32p_row02_traceSegment_094_2268_0013, g32p_row02_traceSegment_094_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2308 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2295 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2295 13 14, g32p_row02_traceSegment_094_2295_0013, g32p_row02_traceSegment_094_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2268 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2268 27 27, g32p_row02_traceSegment_094_2268_0027, g32p_row02_traceSegment_094_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2322 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2322 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2322 13 14, g32p_row02_traceSegment_094_2322_0013, g32p_row02_traceSegment_094_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2349 13 14, g32p_row02_traceSegment_094_2349_0013, g32p_row02_traceSegment_094_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2322 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2322 27 27, g32p_row02_traceSegment_094_2322_0027, g32p_row02_traceSegment_094_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2268 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2268 54 54, g32p_row02_traceSegment_094_2268_0054, g32p_row02_traceSegment_094_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 2160 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2160 108 108, g32p_row02_traceSegment_094_2160_0108, g32p_row02_traceSegment_094_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2376 13 14, g32p_row02_traceSegment_094_2376_0013, g32p_row02_traceSegment_094_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2403 13 14, g32p_row02_traceSegment_094_2403_0013, g32p_row02_traceSegment_094_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2376 27 27, g32p_row02_traceSegment_094_2376_0027, g32p_row02_traceSegment_094_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2430 13 14, g32p_row02_traceSegment_094_2430_0013, g32p_row02_traceSegment_094_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2457 13 14, g32p_row02_traceSegment_094_2457_0013, g32p_row02_traceSegment_094_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2430 27 27, g32p_row02_traceSegment_094_2430_0027, g32p_row02_traceSegment_094_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2376 54 54, g32p_row02_traceSegment_094_2376_0054, g32p_row02_traceSegment_094_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2484 13 14, g32p_row02_traceSegment_094_2484_0013, g32p_row02_traceSegment_094_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2511 13 14, g32p_row02_traceSegment_094_2511_0013, g32p_row02_traceSegment_094_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2484 27 27, g32p_row02_traceSegment_094_2484_0027, g32p_row02_traceSegment_094_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2538 13 14, g32p_row02_traceSegment_094_2538_0013, g32p_row02_traceSegment_094_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2565 13 14, g32p_row02_traceSegment_094_2565_0013, g32p_row02_traceSegment_094_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2538 27 27, g32p_row02_traceSegment_094_2538_0027, g32p_row02_traceSegment_094_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2484 54 54, g32p_row02_traceSegment_094_2484_0054, g32p_row02_traceSegment_094_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2376 108 108, g32p_row02_traceSegment_094_2376_0108, g32p_row02_traceSegment_094_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 2160 432 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2160 216 216, g32p_row02_traceSegment_094_2160_0216, g32p_row02_traceSegment_094_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 864 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1728 432 432, g32p_row02_traceSegment_094_1728_0432, g32p_row02_traceSegment_094_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2592 13 14, g32p_row02_traceSegment_094_2592_0013, g32p_row02_traceSegment_094_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2619 13 14, g32p_row02_traceSegment_094_2619_0013, g32p_row02_traceSegment_094_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2592 27 27, g32p_row02_traceSegment_094_2592_0027, g32p_row02_traceSegment_094_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2646 13 14, g32p_row02_traceSegment_094_2646_0013, g32p_row02_traceSegment_094_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2673 13 14, g32p_row02_traceSegment_094_2673_0013, g32p_row02_traceSegment_094_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2646 27 27, g32p_row02_traceSegment_094_2646_0027, g32p_row02_traceSegment_094_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2592 54 54, g32p_row02_traceSegment_094_2592_0054, g32p_row02_traceSegment_094_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2700 13 14, g32p_row02_traceSegment_094_2700_0013, g32p_row02_traceSegment_094_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2727 13 14, g32p_row02_traceSegment_094_2727_0013, g32p_row02_traceSegment_094_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2700 27 27, g32p_row02_traceSegment_094_2700_0027, g32p_row02_traceSegment_094_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2754 13 14, g32p_row02_traceSegment_094_2754_0013, g32p_row02_traceSegment_094_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2781 13 14, g32p_row02_traceSegment_094_2781_0013, g32p_row02_traceSegment_094_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2754 27 27, g32p_row02_traceSegment_094_2754_0027, g32p_row02_traceSegment_094_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2700 54 54, g32p_row02_traceSegment_094_2700_0054, g32p_row02_traceSegment_094_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2592 108 108, g32p_row02_traceSegment_094_2592_0108, g32p_row02_traceSegment_094_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2808 13 14, g32p_row02_traceSegment_094_2808_0013, g32p_row02_traceSegment_094_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2835 13 14, g32p_row02_traceSegment_094_2835_0013, g32p_row02_traceSegment_094_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2808 27 27, g32p_row02_traceSegment_094_2808_0027, g32p_row02_traceSegment_094_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2862 13 14, g32p_row02_traceSegment_094_2862_0013, g32p_row02_traceSegment_094_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2889 13 14, g32p_row02_traceSegment_094_2889_0013, g32p_row02_traceSegment_094_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2862 27 27, g32p_row02_traceSegment_094_2862_0027, g32p_row02_traceSegment_094_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2808 54 54, g32p_row02_traceSegment_094_2808_0054, g32p_row02_traceSegment_094_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2916 13 14, g32p_row02_traceSegment_094_2916_0013, g32p_row02_traceSegment_094_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2943 13 14, g32p_row02_traceSegment_094_2943_0013, g32p_row02_traceSegment_094_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2916 27 27, g32p_row02_traceSegment_094_2916_0027, g32p_row02_traceSegment_094_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2970 13 14, g32p_row02_traceSegment_094_2970_0013, g32p_row02_traceSegment_094_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2997 13 14, g32p_row02_traceSegment_094_2997_0013, g32p_row02_traceSegment_094_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2970 27 27, g32p_row02_traceSegment_094_2970_0027, g32p_row02_traceSegment_094_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2916 54 54, g32p_row02_traceSegment_094_2916_0054, g32p_row02_traceSegment_094_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2808 108 108, g32p_row02_traceSegment_094_2808_0108, g32p_row02_traceSegment_094_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2592 216 216, g32p_row02_traceSegment_094_2592_0216, g32p_row02_traceSegment_094_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3024 13 14, g32p_row02_traceSegment_094_3024_0013, g32p_row02_traceSegment_094_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3051 13 14, g32p_row02_traceSegment_094_3051_0013, g32p_row02_traceSegment_094_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3024 27 27, g32p_row02_traceSegment_094_3024_0027, g32p_row02_traceSegment_094_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3078 13 14, g32p_row02_traceSegment_094_3078_0013, g32p_row02_traceSegment_094_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3105 13 14, g32p_row02_traceSegment_094_3105_0013, g32p_row02_traceSegment_094_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3078 27 27, g32p_row02_traceSegment_094_3078_0027, g32p_row02_traceSegment_094_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3024 54 54, g32p_row02_traceSegment_094_3024_0054, g32p_row02_traceSegment_094_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3132 13 14, g32p_row02_traceSegment_094_3132_0013, g32p_row02_traceSegment_094_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3159 13 14, g32p_row02_traceSegment_094_3159_0013, g32p_row02_traceSegment_094_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3132 27 27, g32p_row02_traceSegment_094_3132_0027, g32p_row02_traceSegment_094_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3186 13 14, g32p_row02_traceSegment_094_3186_0013, g32p_row02_traceSegment_094_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3213 13 14, g32p_row02_traceSegment_094_3213_0013, g32p_row02_traceSegment_094_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3186 27 27, g32p_row02_traceSegment_094_3186_0027, g32p_row02_traceSegment_094_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3132 54 54, g32p_row02_traceSegment_094_3132_0054, g32p_row02_traceSegment_094_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3024 108 108, g32p_row02_traceSegment_094_3024_0108, g32p_row02_traceSegment_094_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3240 13 14, g32p_row02_traceSegment_094_3240_0013, g32p_row02_traceSegment_094_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3267 13 14, g32p_row02_traceSegment_094_3267_0013, g32p_row02_traceSegment_094_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3240 27 27, g32p_row02_traceSegment_094_3240_0027, g32p_row02_traceSegment_094_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3294 13 14, g32p_row02_traceSegment_094_3294_0013, g32p_row02_traceSegment_094_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3321 13 14, g32p_row02_traceSegment_094_3321_0013, g32p_row02_traceSegment_094_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3294 27 27, g32p_row02_traceSegment_094_3294_0027, g32p_row02_traceSegment_094_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3240 54 54, g32p_row02_traceSegment_094_3240_0054, g32p_row02_traceSegment_094_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3348 13 14, g32p_row02_traceSegment_094_3348_0013, g32p_row02_traceSegment_094_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3375 13 14, g32p_row02_traceSegment_094_3375_0013, g32p_row02_traceSegment_094_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3348 27 27, g32p_row02_traceSegment_094_3348_0027, g32p_row02_traceSegment_094_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3402 13 14, g32p_row02_traceSegment_094_3402_0013, g32p_row02_traceSegment_094_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_094 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_094 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_094_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_094 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3429 13 14, g32p_row02_traceSegment_094_3429_0013, g32p_row02_traceSegment_094_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_094 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3402 27 27, g32p_row02_traceSegment_094_3402_0027, g32p_row02_traceSegment_094_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_094 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3348 54 54, g32p_row02_traceSegment_094_3348_0054, g32p_row02_traceSegment_094_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_094 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3240 108 108, g32p_row02_traceSegment_094_3240_0108, g32p_row02_traceSegment_094_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_094_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_094 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 3024 216 216, g32p_row02_traceSegment_094_3024_0216, g32p_row02_traceSegment_094_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_094_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_094 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 2592 432 432, g32p_row02_traceSegment_094_2592_0432, g32p_row02_traceSegment_094_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_094_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_094 1728 1728 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 1728 864 864, g32p_row02_traceSegment_094_1728_0864, g32p_row02_traceSegment_094_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_094_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_094 0 3456 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_094 0 1728 1728, g32p_row02_traceSegment_094_0000_1728, g32p_row02_traceSegment_094_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 94 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_094_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_095 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 95 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_095_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 13 14, g32p_row02_traceSegment_095_0000_0013, g32p_row02_traceSegment_095_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 27 13 14, g32p_row02_traceSegment_095_0027_0013, g32p_row02_traceSegment_095_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 27 27, g32p_row02_traceSegment_095_0000_0027, g32p_row02_traceSegment_095_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 54 13 14, g32p_row02_traceSegment_095_0054_0013, g32p_row02_traceSegment_095_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 81 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 94 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 81 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 81 13 14, g32p_row02_traceSegment_095_0081_0013, g32p_row02_traceSegment_095_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 54 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 54 27 27, g32p_row02_traceSegment_095_0054_0027, g32p_row02_traceSegment_095_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 0 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 54 54, g32p_row02_traceSegment_095_0000_0054, g32p_row02_traceSegment_095_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 108 13 14, g32p_row02_traceSegment_095_0108_0013, g32p_row02_traceSegment_095_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 135 13 14, g32p_row02_traceSegment_095_0135_0013, g32p_row02_traceSegment_095_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 108 27 27, g32p_row02_traceSegment_095_0108_0027, g32p_row02_traceSegment_095_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 162 13 14, g32p_row02_traceSegment_095_0162_0013, g32p_row02_traceSegment_095_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 189 13 14, g32p_row02_traceSegment_095_0189_0013, g32p_row02_traceSegment_095_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 162 27 27, g32p_row02_traceSegment_095_0162_0027, g32p_row02_traceSegment_095_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 108 54 54, g32p_row02_traceSegment_095_0108_0054, g32p_row02_traceSegment_095_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 0 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 108 108, g32p_row02_traceSegment_095_0000_0108, g32p_row02_traceSegment_095_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 216 13 14, g32p_row02_traceSegment_095_0216_0013, g32p_row02_traceSegment_095_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 243 13 14, g32p_row02_traceSegment_095_0243_0013, g32p_row02_traceSegment_095_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 216 27 27, g32p_row02_traceSegment_095_0216_0027, g32p_row02_traceSegment_095_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 270 13 14, g32p_row02_traceSegment_095_0270_0013, g32p_row02_traceSegment_095_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 297 13 14, g32p_row02_traceSegment_095_0297_0013, g32p_row02_traceSegment_095_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 270 27 27, g32p_row02_traceSegment_095_0270_0027, g32p_row02_traceSegment_095_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 216 54 54, g32p_row02_traceSegment_095_0216_0054, g32p_row02_traceSegment_095_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 324 13 14, g32p_row02_traceSegment_095_0324_0013, g32p_row02_traceSegment_095_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 351 13 14, g32p_row02_traceSegment_095_0351_0013, g32p_row02_traceSegment_095_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 324 27 27, g32p_row02_traceSegment_095_0324_0027, g32p_row02_traceSegment_095_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 378 13 14, g32p_row02_traceSegment_095_0378_0013, g32p_row02_traceSegment_095_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 405 13 14, g32p_row02_traceSegment_095_0405_0013, g32p_row02_traceSegment_095_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 378 27 27, g32p_row02_traceSegment_095_0378_0027, g32p_row02_traceSegment_095_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 324 54 54, g32p_row02_traceSegment_095_0324_0054, g32p_row02_traceSegment_095_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 216 108 108, g32p_row02_traceSegment_095_0216_0108, g32p_row02_traceSegment_095_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 0 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 216 216, g32p_row02_traceSegment_095_0000_0216, g32p_row02_traceSegment_095_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 432 13 14, g32p_row02_traceSegment_095_0432_0013, g32p_row02_traceSegment_095_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 472 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 459 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 459 13 14, g32p_row02_traceSegment_095_0459_0013, g32p_row02_traceSegment_095_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 432 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 432 27 27, g32p_row02_traceSegment_095_0432_0027, g32p_row02_traceSegment_095_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 486 13 14, g32p_row02_traceSegment_095_0486_0013, g32p_row02_traceSegment_095_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 513 13 14, g32p_row02_traceSegment_095_0513_0013, g32p_row02_traceSegment_095_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 486 27 27, g32p_row02_traceSegment_095_0486_0027, g32p_row02_traceSegment_095_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 432 54 54, g32p_row02_traceSegment_095_0432_0054, g32p_row02_traceSegment_095_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 540 13 14, g32p_row02_traceSegment_095_0540_0013, g32p_row02_traceSegment_095_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 567 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 567 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 567 13 14, g32p_row02_traceSegment_095_0567_0013, g32p_row02_traceSegment_095_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 540 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 540 27 27, g32p_row02_traceSegment_095_0540_0027, g32p_row02_traceSegment_095_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 594 13 14, g32p_row02_traceSegment_095_0594_0013, g32p_row02_traceSegment_095_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 621 13 14, g32p_row02_traceSegment_095_0621_0013, g32p_row02_traceSegment_095_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 594 27 27, g32p_row02_traceSegment_095_0594_0027, g32p_row02_traceSegment_095_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 540 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 540 54 54, g32p_row02_traceSegment_095_0540_0054, g32p_row02_traceSegment_095_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 432 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 432 108 108, g32p_row02_traceSegment_095_0432_0108, g32p_row02_traceSegment_095_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 648 13 14, g32p_row02_traceSegment_095_0648_0013, g32p_row02_traceSegment_095_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 675 13 14, g32p_row02_traceSegment_095_0675_0013, g32p_row02_traceSegment_095_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 648 27 27, g32p_row02_traceSegment_095_0648_0027, g32p_row02_traceSegment_095_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 702 13 14, g32p_row02_traceSegment_095_0702_0013, g32p_row02_traceSegment_095_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 729 13 14, g32p_row02_traceSegment_095_0729_0013, g32p_row02_traceSegment_095_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 702 27 27, g32p_row02_traceSegment_095_0702_0027, g32p_row02_traceSegment_095_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 648 54 54, g32p_row02_traceSegment_095_0648_0054, g32p_row02_traceSegment_095_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 756 13 14, g32p_row02_traceSegment_095_0756_0013, g32p_row02_traceSegment_095_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 783 13 14, g32p_row02_traceSegment_095_0783_0013, g32p_row02_traceSegment_095_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 756 27 27, g32p_row02_traceSegment_095_0756_0027, g32p_row02_traceSegment_095_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 810 13 14, g32p_row02_traceSegment_095_0810_0013, g32p_row02_traceSegment_095_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 837 13 14, g32p_row02_traceSegment_095_0837_0013, g32p_row02_traceSegment_095_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 810 27 27, g32p_row02_traceSegment_095_0810_0027, g32p_row02_traceSegment_095_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 756 54 54, g32p_row02_traceSegment_095_0756_0054, g32p_row02_traceSegment_095_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 648 108 108, g32p_row02_traceSegment_095_0648_0108, g32p_row02_traceSegment_095_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 432 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 432 216 216, g32p_row02_traceSegment_095_0432_0216, g32p_row02_traceSegment_095_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_095 0 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 432 432, g32p_row02_traceSegment_095_0000_0432, g32p_row02_traceSegment_095_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 864 13 14, g32p_row02_traceSegment_095_0864_0013, g32p_row02_traceSegment_095_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 891 13 14, g32p_row02_traceSegment_095_0891_0013, g32p_row02_traceSegment_095_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 864 27 27, g32p_row02_traceSegment_095_0864_0027, g32p_row02_traceSegment_095_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 918 13 14, g32p_row02_traceSegment_095_0918_0013, g32p_row02_traceSegment_095_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 945 13 14, g32p_row02_traceSegment_095_0945_0013, g32p_row02_traceSegment_095_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 918 27 27, g32p_row02_traceSegment_095_0918_0027, g32p_row02_traceSegment_095_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 864 54 54, g32p_row02_traceSegment_095_0864_0054, g32p_row02_traceSegment_095_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 972 13 14, g32p_row02_traceSegment_095_0972_0013, g32p_row02_traceSegment_095_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 999 13 14, g32p_row02_traceSegment_095_0999_0013, g32p_row02_traceSegment_095_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 972 27 27, g32p_row02_traceSegment_095_0972_0027, g32p_row02_traceSegment_095_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1026 13 14, g32p_row02_traceSegment_095_1026_0013, g32p_row02_traceSegment_095_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1053 13 14, g32p_row02_traceSegment_095_1053_0013, g32p_row02_traceSegment_095_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1026 27 27, g32p_row02_traceSegment_095_1026_0027, g32p_row02_traceSegment_095_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 972 54 54, g32p_row02_traceSegment_095_0972_0054, g32p_row02_traceSegment_095_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 864 108 108, g32p_row02_traceSegment_095_0864_0108, g32p_row02_traceSegment_095_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1080 13 14, g32p_row02_traceSegment_095_1080_0013, g32p_row02_traceSegment_095_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1107 13 14, g32p_row02_traceSegment_095_1107_0013, g32p_row02_traceSegment_095_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1080 27 27, g32p_row02_traceSegment_095_1080_0027, g32p_row02_traceSegment_095_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1134 13 14, g32p_row02_traceSegment_095_1134_0013, g32p_row02_traceSegment_095_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1161 13 14, g32p_row02_traceSegment_095_1161_0013, g32p_row02_traceSegment_095_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1134 27 27, g32p_row02_traceSegment_095_1134_0027, g32p_row02_traceSegment_095_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1080 54 54, g32p_row02_traceSegment_095_1080_0054, g32p_row02_traceSegment_095_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1188 13 14, g32p_row02_traceSegment_095_1188_0013, g32p_row02_traceSegment_095_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1215 13 14, g32p_row02_traceSegment_095_1215_0013, g32p_row02_traceSegment_095_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1188 27 27, g32p_row02_traceSegment_095_1188_0027, g32p_row02_traceSegment_095_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1242 13 14, g32p_row02_traceSegment_095_1242_0013, g32p_row02_traceSegment_095_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1269 13 14, g32p_row02_traceSegment_095_1269_0013, g32p_row02_traceSegment_095_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1242 27 27, g32p_row02_traceSegment_095_1242_0027, g32p_row02_traceSegment_095_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1188 54 54, g32p_row02_traceSegment_095_1188_0054, g32p_row02_traceSegment_095_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1080 108 108, g32p_row02_traceSegment_095_1080_0108, g32p_row02_traceSegment_095_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 864 216 216, g32p_row02_traceSegment_095_0864_0216, g32p_row02_traceSegment_095_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1309 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1296 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1296 13 14, g32p_row02_traceSegment_095_1296_0013, g32p_row02_traceSegment_095_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1323 13 14, g32p_row02_traceSegment_095_1323_0013, g32p_row02_traceSegment_095_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1296 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1296 27 27, g32p_row02_traceSegment_095_1296_0027, g32p_row02_traceSegment_095_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1350 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1350 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1350 13 14, g32p_row02_traceSegment_095_1350_0013, g32p_row02_traceSegment_095_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1377 13 14, g32p_row02_traceSegment_095_1377_0013, g32p_row02_traceSegment_095_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1350 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1350 27 27, g32p_row02_traceSegment_095_1350_0027, g32p_row02_traceSegment_095_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1296 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1296 54 54, g32p_row02_traceSegment_095_1296_0054, g32p_row02_traceSegment_095_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1404 13 14, g32p_row02_traceSegment_095_1404_0013, g32p_row02_traceSegment_095_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1431 13 14, g32p_row02_traceSegment_095_1431_0013, g32p_row02_traceSegment_095_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1404 27 27, g32p_row02_traceSegment_095_1404_0027, g32p_row02_traceSegment_095_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1458 13 14, g32p_row02_traceSegment_095_1458_0013, g32p_row02_traceSegment_095_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1485 13 14, g32p_row02_traceSegment_095_1485_0013, g32p_row02_traceSegment_095_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1458 27 27, g32p_row02_traceSegment_095_1458_0027, g32p_row02_traceSegment_095_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1404 54 54, g32p_row02_traceSegment_095_1404_0054, g32p_row02_traceSegment_095_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 1296 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1296 108 108, g32p_row02_traceSegment_095_1296_0108, g32p_row02_traceSegment_095_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1512 13 14, g32p_row02_traceSegment_095_1512_0013, g32p_row02_traceSegment_095_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1539 13 14, g32p_row02_traceSegment_095_1539_0013, g32p_row02_traceSegment_095_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1512 27 27, g32p_row02_traceSegment_095_1512_0027, g32p_row02_traceSegment_095_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1566 13 14, g32p_row02_traceSegment_095_1566_0013, g32p_row02_traceSegment_095_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1593 13 14, g32p_row02_traceSegment_095_1593_0013, g32p_row02_traceSegment_095_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1566 27 27, g32p_row02_traceSegment_095_1566_0027, g32p_row02_traceSegment_095_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1512 54 54, g32p_row02_traceSegment_095_1512_0054, g32p_row02_traceSegment_095_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1620 13 14, g32p_row02_traceSegment_095_1620_0013, g32p_row02_traceSegment_095_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1647 13 14, g32p_row02_traceSegment_095_1647_0013, g32p_row02_traceSegment_095_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1620 27 27, g32p_row02_traceSegment_095_1620_0027, g32p_row02_traceSegment_095_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1674 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1674 13 14, g32p_row02_traceSegment_095_1674_0013, g32p_row02_traceSegment_095_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1701 13 14, g32p_row02_traceSegment_095_1701_0013, g32p_row02_traceSegment_095_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1674 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1674 27 27, g32p_row02_traceSegment_095_1674_0027, g32p_row02_traceSegment_095_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1620 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1620 54 54, g32p_row02_traceSegment_095_1620_0054, g32p_row02_traceSegment_095_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 1512 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1512 108 108, g32p_row02_traceSegment_095_1512_0108, g32p_row02_traceSegment_095_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 1296 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1296 216 216, g32p_row02_traceSegment_095_1296_0216, g32p_row02_traceSegment_095_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_095 864 864 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 864 432 432, g32p_row02_traceSegment_095_0864_0432, g32p_row02_traceSegment_095_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_095 0 1728 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 864 864, g32p_row02_traceSegment_095_0000_0864, g32p_row02_traceSegment_095_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1728 13 14, g32p_row02_traceSegment_095_1728_0013, g32p_row02_traceSegment_095_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1755 13 14, g32p_row02_traceSegment_095_1755_0013, g32p_row02_traceSegment_095_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1728 27 27, g32p_row02_traceSegment_095_1728_0027, g32p_row02_traceSegment_095_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1782 13 14, g32p_row02_traceSegment_095_1782_0013, g32p_row02_traceSegment_095_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1809 13 14, g32p_row02_traceSegment_095_1809_0013, g32p_row02_traceSegment_095_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1782 27 27, g32p_row02_traceSegment_095_1782_0027, g32p_row02_traceSegment_095_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1728 54 54, g32p_row02_traceSegment_095_1728_0054, g32p_row02_traceSegment_095_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1836 13 14, g32p_row02_traceSegment_095_1836_0013, g32p_row02_traceSegment_095_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1863 13 14, g32p_row02_traceSegment_095_1863_0013, g32p_row02_traceSegment_095_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1836 27 27, g32p_row02_traceSegment_095_1836_0027, g32p_row02_traceSegment_095_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1890 13 14, g32p_row02_traceSegment_095_1890_0013, g32p_row02_traceSegment_095_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1917 13 14, g32p_row02_traceSegment_095_1917_0013, g32p_row02_traceSegment_095_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1890 27 27, g32p_row02_traceSegment_095_1890_0027, g32p_row02_traceSegment_095_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1836 54 54, g32p_row02_traceSegment_095_1836_0054, g32p_row02_traceSegment_095_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1728 108 108, g32p_row02_traceSegment_095_1728_0108, g32p_row02_traceSegment_095_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1944 13 14, g32p_row02_traceSegment_095_1944_0013, g32p_row02_traceSegment_095_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 1984 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1971 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1971 13 14, g32p_row02_traceSegment_095_1971_0013, g32p_row02_traceSegment_095_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1944 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1944 27 27, g32p_row02_traceSegment_095_1944_0027, g32p_row02_traceSegment_095_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1998 13 14, g32p_row02_traceSegment_095_1998_0013, g32p_row02_traceSegment_095_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2025 13 14, g32p_row02_traceSegment_095_2025_0013, g32p_row02_traceSegment_095_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1998 27 27, g32p_row02_traceSegment_095_1998_0027, g32p_row02_traceSegment_095_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 1944 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1944 54 54, g32p_row02_traceSegment_095_1944_0054, g32p_row02_traceSegment_095_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2052 13 14, g32p_row02_traceSegment_095_2052_0013, g32p_row02_traceSegment_095_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2079 13 14, g32p_row02_traceSegment_095_2079_0013, g32p_row02_traceSegment_095_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2052 27 27, g32p_row02_traceSegment_095_2052_0027, g32p_row02_traceSegment_095_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2106 13 14, g32p_row02_traceSegment_095_2106_0013, g32p_row02_traceSegment_095_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2133 13 14, g32p_row02_traceSegment_095_2133_0013, g32p_row02_traceSegment_095_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2106 27 27, g32p_row02_traceSegment_095_2106_0027, g32p_row02_traceSegment_095_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2052 54 54, g32p_row02_traceSegment_095_2052_0054, g32p_row02_traceSegment_095_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 1944 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1944 108 108, g32p_row02_traceSegment_095_1944_0108, g32p_row02_traceSegment_095_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1728 216 216, g32p_row02_traceSegment_095_1728_0216, g32p_row02_traceSegment_095_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2160 13 14, g32p_row02_traceSegment_095_2160_0013, g32p_row02_traceSegment_095_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2187 13 14, g32p_row02_traceSegment_095_2187_0013, g32p_row02_traceSegment_095_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2160 27 27, g32p_row02_traceSegment_095_2160_0027, g32p_row02_traceSegment_095_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2214 13 14, g32p_row02_traceSegment_095_2214_0013, g32p_row02_traceSegment_095_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2241 13 14, g32p_row02_traceSegment_095_2241_0013, g32p_row02_traceSegment_095_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2214 27 27, g32p_row02_traceSegment_095_2214_0027, g32p_row02_traceSegment_095_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2160 54 54, g32p_row02_traceSegment_095_2160_0054, g32p_row02_traceSegment_095_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2268 13 14, g32p_row02_traceSegment_095_2268_0013, g32p_row02_traceSegment_095_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2295 13 14, g32p_row02_traceSegment_095_2295_0013, g32p_row02_traceSegment_095_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2268 27 27, g32p_row02_traceSegment_095_2268_0027, g32p_row02_traceSegment_095_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2322 13 14, g32p_row02_traceSegment_095_2322_0013, g32p_row02_traceSegment_095_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2349 13 14, g32p_row02_traceSegment_095_2349_0013, g32p_row02_traceSegment_095_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2322 27 27, g32p_row02_traceSegment_095_2322_0027, g32p_row02_traceSegment_095_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2268 54 54, g32p_row02_traceSegment_095_2268_0054, g32p_row02_traceSegment_095_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2160 108 108, g32p_row02_traceSegment_095_2160_0108, g32p_row02_traceSegment_095_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2376 13 14, g32p_row02_traceSegment_095_2376_0013, g32p_row02_traceSegment_095_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2403 13 14, g32p_row02_traceSegment_095_2403_0013, g32p_row02_traceSegment_095_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2376 27 27, g32p_row02_traceSegment_095_2376_0027, g32p_row02_traceSegment_095_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2430 13 14, g32p_row02_traceSegment_095_2430_0013, g32p_row02_traceSegment_095_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2457 13 14, g32p_row02_traceSegment_095_2457_0013, g32p_row02_traceSegment_095_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2430 27 27, g32p_row02_traceSegment_095_2430_0027, g32p_row02_traceSegment_095_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2376 54 54, g32p_row02_traceSegment_095_2376_0054, g32p_row02_traceSegment_095_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2484 13 14, g32p_row02_traceSegment_095_2484_0013, g32p_row02_traceSegment_095_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2511 13 14, g32p_row02_traceSegment_095_2511_0013, g32p_row02_traceSegment_095_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2484 27 27, g32p_row02_traceSegment_095_2484_0027, g32p_row02_traceSegment_095_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2538 13 14, g32p_row02_traceSegment_095_2538_0013, g32p_row02_traceSegment_095_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2565 13 14, g32p_row02_traceSegment_095_2565_0013, g32p_row02_traceSegment_095_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2538 27 27, g32p_row02_traceSegment_095_2538_0027, g32p_row02_traceSegment_095_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2484 54 54, g32p_row02_traceSegment_095_2484_0054, g32p_row02_traceSegment_095_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2376 108 108, g32p_row02_traceSegment_095_2376_0108, g32p_row02_traceSegment_095_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2160 216 216, g32p_row02_traceSegment_095_2160_0216, g32p_row02_traceSegment_095_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1728 432 432, g32p_row02_traceSegment_095_1728_0432, g32p_row02_traceSegment_095_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2592 13 14, g32p_row02_traceSegment_095_2592_0013, g32p_row02_traceSegment_095_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2619 13 14, g32p_row02_traceSegment_095_2619_0013, g32p_row02_traceSegment_095_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2592 27 27, g32p_row02_traceSegment_095_2592_0027, g32p_row02_traceSegment_095_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2646 13 14, g32p_row02_traceSegment_095_2646_0013, g32p_row02_traceSegment_095_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2673 13 14, g32p_row02_traceSegment_095_2673_0013, g32p_row02_traceSegment_095_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2646 27 27, g32p_row02_traceSegment_095_2646_0027, g32p_row02_traceSegment_095_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2592 54 54, g32p_row02_traceSegment_095_2592_0054, g32p_row02_traceSegment_095_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2700 13 14, g32p_row02_traceSegment_095_2700_0013, g32p_row02_traceSegment_095_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2727 13 14, g32p_row02_traceSegment_095_2727_0013, g32p_row02_traceSegment_095_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2700 27 27, g32p_row02_traceSegment_095_2700_0027, g32p_row02_traceSegment_095_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2754 13 14, g32p_row02_traceSegment_095_2754_0013, g32p_row02_traceSegment_095_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2781 13 14, g32p_row02_traceSegment_095_2781_0013, g32p_row02_traceSegment_095_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2754 27 27, g32p_row02_traceSegment_095_2754_0027, g32p_row02_traceSegment_095_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2700 54 54, g32p_row02_traceSegment_095_2700_0054, g32p_row02_traceSegment_095_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2592 108 108, g32p_row02_traceSegment_095_2592_0108, g32p_row02_traceSegment_095_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2808 13 14, g32p_row02_traceSegment_095_2808_0013, g32p_row02_traceSegment_095_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2835 13 14, g32p_row02_traceSegment_095_2835_0013, g32p_row02_traceSegment_095_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2808 27 27, g32p_row02_traceSegment_095_2808_0027, g32p_row02_traceSegment_095_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2862 13 14, g32p_row02_traceSegment_095_2862_0013, g32p_row02_traceSegment_095_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2889 13 14, g32p_row02_traceSegment_095_2889_0013, g32p_row02_traceSegment_095_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2862 27 27, g32p_row02_traceSegment_095_2862_0027, g32p_row02_traceSegment_095_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2808 54 54, g32p_row02_traceSegment_095_2808_0054, g32p_row02_traceSegment_095_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2916 13 14, g32p_row02_traceSegment_095_2916_0013, g32p_row02_traceSegment_095_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2943 13 14, g32p_row02_traceSegment_095_2943_0013, g32p_row02_traceSegment_095_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2916 27 27, g32p_row02_traceSegment_095_2916_0027, g32p_row02_traceSegment_095_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2970 13 14, g32p_row02_traceSegment_095_2970_0013, g32p_row02_traceSegment_095_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2997 13 14, g32p_row02_traceSegment_095_2997_0013, g32p_row02_traceSegment_095_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2970 27 27, g32p_row02_traceSegment_095_2970_0027, g32p_row02_traceSegment_095_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2916 54 54, g32p_row02_traceSegment_095_2916_0054, g32p_row02_traceSegment_095_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2808 108 108, g32p_row02_traceSegment_095_2808_0108, g32p_row02_traceSegment_095_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2592 216 216, g32p_row02_traceSegment_095_2592_0216, g32p_row02_traceSegment_095_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3024 13 14, g32p_row02_traceSegment_095_3024_0013, g32p_row02_traceSegment_095_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3051 13 14, g32p_row02_traceSegment_095_3051_0013, g32p_row02_traceSegment_095_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3024 27 27, g32p_row02_traceSegment_095_3024_0027, g32p_row02_traceSegment_095_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3078 13 14, g32p_row02_traceSegment_095_3078_0013, g32p_row02_traceSegment_095_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3105 13 14, g32p_row02_traceSegment_095_3105_0013, g32p_row02_traceSegment_095_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3078 27 27, g32p_row02_traceSegment_095_3078_0027, g32p_row02_traceSegment_095_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3024 54 54, g32p_row02_traceSegment_095_3024_0054, g32p_row02_traceSegment_095_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3132 13 14, g32p_row02_traceSegment_095_3132_0013, g32p_row02_traceSegment_095_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3159 13 14, g32p_row02_traceSegment_095_3159_0013, g32p_row02_traceSegment_095_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3132 27 27, g32p_row02_traceSegment_095_3132_0027, g32p_row02_traceSegment_095_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3186 13 14, g32p_row02_traceSegment_095_3186_0013, g32p_row02_traceSegment_095_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3213 13 14, g32p_row02_traceSegment_095_3213_0013, g32p_row02_traceSegment_095_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3186 27 27, g32p_row02_traceSegment_095_3186_0027, g32p_row02_traceSegment_095_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3132 54 54, g32p_row02_traceSegment_095_3132_0054, g32p_row02_traceSegment_095_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3024 108 108, g32p_row02_traceSegment_095_3024_0108, g32p_row02_traceSegment_095_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3240 13 14, g32p_row02_traceSegment_095_3240_0013, g32p_row02_traceSegment_095_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3267 13 14, g32p_row02_traceSegment_095_3267_0013, g32p_row02_traceSegment_095_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3240 27 27, g32p_row02_traceSegment_095_3240_0027, g32p_row02_traceSegment_095_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3294 13 14, g32p_row02_traceSegment_095_3294_0013, g32p_row02_traceSegment_095_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3321 13 14, g32p_row02_traceSegment_095_3321_0013, g32p_row02_traceSegment_095_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3294 27 27, g32p_row02_traceSegment_095_3294_0027, g32p_row02_traceSegment_095_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3240 54 54, g32p_row02_traceSegment_095_3240_0054, g32p_row02_traceSegment_095_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3348 13 14, g32p_row02_traceSegment_095_3348_0013, g32p_row02_traceSegment_095_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3375 13 14, g32p_row02_traceSegment_095_3375_0013, g32p_row02_traceSegment_095_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3348 27 27, g32p_row02_traceSegment_095_3348_0027, g32p_row02_traceSegment_095_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3402 13 14, g32p_row02_traceSegment_095_3402_0013, g32p_row02_traceSegment_095_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_095 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_095 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_095_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_095 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3429 13 14, g32p_row02_traceSegment_095_3429_0013, g32p_row02_traceSegment_095_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_095 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3402 27 27, g32p_row02_traceSegment_095_3402_0027, g32p_row02_traceSegment_095_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_095 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3348 54 54, g32p_row02_traceSegment_095_3348_0054, g32p_row02_traceSegment_095_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_095 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3240 108 108, g32p_row02_traceSegment_095_3240_0108, g32p_row02_traceSegment_095_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_095_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_095 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 3024 216 216, g32p_row02_traceSegment_095_3024_0216, g32p_row02_traceSegment_095_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_095_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_095 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 2592 432 432, g32p_row02_traceSegment_095_2592_0432, g32p_row02_traceSegment_095_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_095_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_095 1728 1728 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 1728 864 864, g32p_row02_traceSegment_095_1728_0864, g32p_row02_traceSegment_095_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_095_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_095 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_095 0 1728 1728, g32p_row02_traceSegment_095_0000_1728, g32p_row02_traceSegment_095_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 95 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_095_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_096_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 0 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 0 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 13 14, g32p_row02_traceSegment_096_0000_0013, g32p_row02_traceSegment_096_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 27 13 14, g32p_row02_traceSegment_096_0027_0013, g32p_row02_traceSegment_096_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 27 27, g32p_row02_traceSegment_096_0000_0027, g32p_row02_traceSegment_096_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 54 13 14, g32p_row02_traceSegment_096_0054_0013, g32p_row02_traceSegment_096_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 81 13 14, g32p_row02_traceSegment_096_0081_0013, g32p_row02_traceSegment_096_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 54 27 27, g32p_row02_traceSegment_096_0054_0027, g32p_row02_traceSegment_096_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 54 54, g32p_row02_traceSegment_096_0000_0054, g32p_row02_traceSegment_096_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 108 13 14, g32p_row02_traceSegment_096_0108_0013, g32p_row02_traceSegment_096_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 135 13 14, g32p_row02_traceSegment_096_0135_0013, g32p_row02_traceSegment_096_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 108 27 27, g32p_row02_traceSegment_096_0108_0027, g32p_row02_traceSegment_096_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 162 13 14, g32p_row02_traceSegment_096_0162_0013, g32p_row02_traceSegment_096_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 189 13 14, g32p_row02_traceSegment_096_0189_0013, g32p_row02_traceSegment_096_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 162 27 27, g32p_row02_traceSegment_096_0162_0027, g32p_row02_traceSegment_096_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 108 54 54, g32p_row02_traceSegment_096_0108_0054, g32p_row02_traceSegment_096_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 0 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 108 108, g32p_row02_traceSegment_096_0000_0108, g32p_row02_traceSegment_096_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 216 13 14, g32p_row02_traceSegment_096_0216_0013, g32p_row02_traceSegment_096_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 243 13 14, g32p_row02_traceSegment_096_0243_0013, g32p_row02_traceSegment_096_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 216 27 27, g32p_row02_traceSegment_096_0216_0027, g32p_row02_traceSegment_096_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 270 13 14, g32p_row02_traceSegment_096_0270_0013, g32p_row02_traceSegment_096_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 297 13 14, g32p_row02_traceSegment_096_0297_0013, g32p_row02_traceSegment_096_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 270 27 27, g32p_row02_traceSegment_096_0270_0027, g32p_row02_traceSegment_096_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 216 54 54, g32p_row02_traceSegment_096_0216_0054, g32p_row02_traceSegment_096_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 324 13 14, g32p_row02_traceSegment_096_0324_0013, g32p_row02_traceSegment_096_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 351 13 14, g32p_row02_traceSegment_096_0351_0013, g32p_row02_traceSegment_096_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 324 27 27, g32p_row02_traceSegment_096_0324_0027, g32p_row02_traceSegment_096_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 378 13 14, g32p_row02_traceSegment_096_0378_0013, g32p_row02_traceSegment_096_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 405 13 14, g32p_row02_traceSegment_096_0405_0013, g32p_row02_traceSegment_096_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 378 27 27, g32p_row02_traceSegment_096_0378_0027, g32p_row02_traceSegment_096_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 324 54 54, g32p_row02_traceSegment_096_0324_0054, g32p_row02_traceSegment_096_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 216 108 108, g32p_row02_traceSegment_096_0216_0108, g32p_row02_traceSegment_096_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 0 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 216 216, g32p_row02_traceSegment_096_0000_0216, g32p_row02_traceSegment_096_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 432 13 14, g32p_row02_traceSegment_096_0432_0013, g32p_row02_traceSegment_096_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 459 13 14, g32p_row02_traceSegment_096_0459_0013, g32p_row02_traceSegment_096_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 432 27 27, g32p_row02_traceSegment_096_0432_0027, g32p_row02_traceSegment_096_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 486 13 14, g32p_row02_traceSegment_096_0486_0013, g32p_row02_traceSegment_096_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 513 13 14, g32p_row02_traceSegment_096_0513_0013, g32p_row02_traceSegment_096_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 486 27 27, g32p_row02_traceSegment_096_0486_0027, g32p_row02_traceSegment_096_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 432 54 54, g32p_row02_traceSegment_096_0432_0054, g32p_row02_traceSegment_096_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 540 13 14, g32p_row02_traceSegment_096_0540_0013, g32p_row02_traceSegment_096_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 567 13 14, g32p_row02_traceSegment_096_0567_0013, g32p_row02_traceSegment_096_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 540 27 27, g32p_row02_traceSegment_096_0540_0027, g32p_row02_traceSegment_096_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 594 13 14, g32p_row02_traceSegment_096_0594_0013, g32p_row02_traceSegment_096_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 621 13 14, g32p_row02_traceSegment_096_0621_0013, g32p_row02_traceSegment_096_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 594 27 27, g32p_row02_traceSegment_096_0594_0027, g32p_row02_traceSegment_096_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 540 54 54, g32p_row02_traceSegment_096_0540_0054, g32p_row02_traceSegment_096_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 432 108 108, g32p_row02_traceSegment_096_0432_0108, g32p_row02_traceSegment_096_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 648 13 14, g32p_row02_traceSegment_096_0648_0013, g32p_row02_traceSegment_096_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 675 13 14, g32p_row02_traceSegment_096_0675_0013, g32p_row02_traceSegment_096_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 648 27 27, g32p_row02_traceSegment_096_0648_0027, g32p_row02_traceSegment_096_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 702 13 14, g32p_row02_traceSegment_096_0702_0013, g32p_row02_traceSegment_096_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 729 13 14, g32p_row02_traceSegment_096_0729_0013, g32p_row02_traceSegment_096_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 702 27 27, g32p_row02_traceSegment_096_0702_0027, g32p_row02_traceSegment_096_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 648 54 54, g32p_row02_traceSegment_096_0648_0054, g32p_row02_traceSegment_096_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 756 13 14, g32p_row02_traceSegment_096_0756_0013, g32p_row02_traceSegment_096_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 783 13 14, g32p_row02_traceSegment_096_0783_0013, g32p_row02_traceSegment_096_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 756 27 27, g32p_row02_traceSegment_096_0756_0027, g32p_row02_traceSegment_096_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 810 13 14, g32p_row02_traceSegment_096_0810_0013, g32p_row02_traceSegment_096_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 837 13 14, g32p_row02_traceSegment_096_0837_0013, g32p_row02_traceSegment_096_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 810 27 27, g32p_row02_traceSegment_096_0810_0027, g32p_row02_traceSegment_096_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 756 54 54, g32p_row02_traceSegment_096_0756_0054, g32p_row02_traceSegment_096_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 648 108 108, g32p_row02_traceSegment_096_0648_0108, g32p_row02_traceSegment_096_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 432 216 216, g32p_row02_traceSegment_096_0432_0216, g32p_row02_traceSegment_096_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_096 0 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 432 432, g32p_row02_traceSegment_096_0000_0432, g32p_row02_traceSegment_096_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 864 13 14, g32p_row02_traceSegment_096_0864_0013, g32p_row02_traceSegment_096_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 891 13 14, g32p_row02_traceSegment_096_0891_0013, g32p_row02_traceSegment_096_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 864 27 27, g32p_row02_traceSegment_096_0864_0027, g32p_row02_traceSegment_096_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 918 13 14, g32p_row02_traceSegment_096_0918_0013, g32p_row02_traceSegment_096_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 945 13 14, g32p_row02_traceSegment_096_0945_0013, g32p_row02_traceSegment_096_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 918 27 27, g32p_row02_traceSegment_096_0918_0027, g32p_row02_traceSegment_096_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 864 54 54, g32p_row02_traceSegment_096_0864_0054, g32p_row02_traceSegment_096_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 972 13 14, g32p_row02_traceSegment_096_0972_0013, g32p_row02_traceSegment_096_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 999 13 14, g32p_row02_traceSegment_096_0999_0013, g32p_row02_traceSegment_096_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 972 27 27, g32p_row02_traceSegment_096_0972_0027, g32p_row02_traceSegment_096_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1026 13 14, g32p_row02_traceSegment_096_1026_0013, g32p_row02_traceSegment_096_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1053 13 14, g32p_row02_traceSegment_096_1053_0013, g32p_row02_traceSegment_096_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1026 27 27, g32p_row02_traceSegment_096_1026_0027, g32p_row02_traceSegment_096_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 972 54 54, g32p_row02_traceSegment_096_0972_0054, g32p_row02_traceSegment_096_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 864 108 108, g32p_row02_traceSegment_096_0864_0108, g32p_row02_traceSegment_096_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1080 13 14, g32p_row02_traceSegment_096_1080_0013, g32p_row02_traceSegment_096_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1107 13 14, g32p_row02_traceSegment_096_1107_0013, g32p_row02_traceSegment_096_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1080 27 27, g32p_row02_traceSegment_096_1080_0027, g32p_row02_traceSegment_096_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1134 13 14, g32p_row02_traceSegment_096_1134_0013, g32p_row02_traceSegment_096_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1161 13 14, g32p_row02_traceSegment_096_1161_0013, g32p_row02_traceSegment_096_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1134 27 27, g32p_row02_traceSegment_096_1134_0027, g32p_row02_traceSegment_096_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1080 54 54, g32p_row02_traceSegment_096_1080_0054, g32p_row02_traceSegment_096_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1188 13 14, g32p_row02_traceSegment_096_1188_0013, g32p_row02_traceSegment_096_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1215 13 14, g32p_row02_traceSegment_096_1215_0013, g32p_row02_traceSegment_096_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1188 27 27, g32p_row02_traceSegment_096_1188_0027, g32p_row02_traceSegment_096_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1242 13 14, g32p_row02_traceSegment_096_1242_0013, g32p_row02_traceSegment_096_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1269 13 14, g32p_row02_traceSegment_096_1269_0013, g32p_row02_traceSegment_096_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1242 27 27, g32p_row02_traceSegment_096_1242_0027, g32p_row02_traceSegment_096_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1188 54 54, g32p_row02_traceSegment_096_1188_0054, g32p_row02_traceSegment_096_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1080 108 108, g32p_row02_traceSegment_096_1080_0108, g32p_row02_traceSegment_096_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 864 216 216, g32p_row02_traceSegment_096_0864_0216, g32p_row02_traceSegment_096_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1296 13 14, g32p_row02_traceSegment_096_1296_0013, g32p_row02_traceSegment_096_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1323 13 14, g32p_row02_traceSegment_096_1323_0013, g32p_row02_traceSegment_096_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1296 27 27, g32p_row02_traceSegment_096_1296_0027, g32p_row02_traceSegment_096_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1350 13 14, g32p_row02_traceSegment_096_1350_0013, g32p_row02_traceSegment_096_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1377 13 14, g32p_row02_traceSegment_096_1377_0013, g32p_row02_traceSegment_096_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1350 27 27, g32p_row02_traceSegment_096_1350_0027, g32p_row02_traceSegment_096_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1296 54 54, g32p_row02_traceSegment_096_1296_0054, g32p_row02_traceSegment_096_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1404 13 14, g32p_row02_traceSegment_096_1404_0013, g32p_row02_traceSegment_096_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1431 13 14, g32p_row02_traceSegment_096_1431_0013, g32p_row02_traceSegment_096_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1404 27 27, g32p_row02_traceSegment_096_1404_0027, g32p_row02_traceSegment_096_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1458 13 14, g32p_row02_traceSegment_096_1458_0013, g32p_row02_traceSegment_096_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1485 13 14, g32p_row02_traceSegment_096_1485_0013, g32p_row02_traceSegment_096_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1458 27 27, g32p_row02_traceSegment_096_1458_0027, g32p_row02_traceSegment_096_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1404 54 54, g32p_row02_traceSegment_096_1404_0054, g32p_row02_traceSegment_096_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1296 108 108, g32p_row02_traceSegment_096_1296_0108, g32p_row02_traceSegment_096_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1512 13 14, g32p_row02_traceSegment_096_1512_0013, g32p_row02_traceSegment_096_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1539 13 14, g32p_row02_traceSegment_096_1539_0013, g32p_row02_traceSegment_096_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1512 27 27, g32p_row02_traceSegment_096_1512_0027, g32p_row02_traceSegment_096_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1566 13 14, g32p_row02_traceSegment_096_1566_0013, g32p_row02_traceSegment_096_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1593 13 14, g32p_row02_traceSegment_096_1593_0013, g32p_row02_traceSegment_096_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1566 27 27, g32p_row02_traceSegment_096_1566_0027, g32p_row02_traceSegment_096_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1512 54 54, g32p_row02_traceSegment_096_1512_0054, g32p_row02_traceSegment_096_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1620 13 14, g32p_row02_traceSegment_096_1620_0013, g32p_row02_traceSegment_096_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1647 13 14, g32p_row02_traceSegment_096_1647_0013, g32p_row02_traceSegment_096_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1620 27 27, g32p_row02_traceSegment_096_1620_0027, g32p_row02_traceSegment_096_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1674 13 14, g32p_row02_traceSegment_096_1674_0013, g32p_row02_traceSegment_096_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1701 13 14, g32p_row02_traceSegment_096_1701_0013, g32p_row02_traceSegment_096_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1674 27 27, g32p_row02_traceSegment_096_1674_0027, g32p_row02_traceSegment_096_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1620 54 54, g32p_row02_traceSegment_096_1620_0054, g32p_row02_traceSegment_096_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1512 108 108, g32p_row02_traceSegment_096_1512_0108, g32p_row02_traceSegment_096_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1296 216 216, g32p_row02_traceSegment_096_1296_0216, g32p_row02_traceSegment_096_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_096 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 864 432 432, g32p_row02_traceSegment_096_0864_0432, g32p_row02_traceSegment_096_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_096 0 1728 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 864 864, g32p_row02_traceSegment_096_0000_0864, g32p_row02_traceSegment_096_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1728 13 14, g32p_row02_traceSegment_096_1728_0013, g32p_row02_traceSegment_096_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1755 13 14, g32p_row02_traceSegment_096_1755_0013, g32p_row02_traceSegment_096_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1728 27 27, g32p_row02_traceSegment_096_1728_0027, g32p_row02_traceSegment_096_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1782 13 14, g32p_row02_traceSegment_096_1782_0013, g32p_row02_traceSegment_096_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1809 13 14, g32p_row02_traceSegment_096_1809_0013, g32p_row02_traceSegment_096_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1782 27 27, g32p_row02_traceSegment_096_1782_0027, g32p_row02_traceSegment_096_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1728 54 54, g32p_row02_traceSegment_096_1728_0054, g32p_row02_traceSegment_096_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1836 13 14, g32p_row02_traceSegment_096_1836_0013, g32p_row02_traceSegment_096_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1863 13 14, g32p_row02_traceSegment_096_1863_0013, g32p_row02_traceSegment_096_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1836 27 27, g32p_row02_traceSegment_096_1836_0027, g32p_row02_traceSegment_096_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1890 13 14, g32p_row02_traceSegment_096_1890_0013, g32p_row02_traceSegment_096_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1917 13 14, g32p_row02_traceSegment_096_1917_0013, g32p_row02_traceSegment_096_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1890 27 27, g32p_row02_traceSegment_096_1890_0027, g32p_row02_traceSegment_096_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1836 54 54, g32p_row02_traceSegment_096_1836_0054, g32p_row02_traceSegment_096_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1728 108 108, g32p_row02_traceSegment_096_1728_0108, g32p_row02_traceSegment_096_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1944 13 14, g32p_row02_traceSegment_096_1944_0013, g32p_row02_traceSegment_096_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1971 13 14, g32p_row02_traceSegment_096_1971_0013, g32p_row02_traceSegment_096_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1944 27 27, g32p_row02_traceSegment_096_1944_0027, g32p_row02_traceSegment_096_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1998 13 14, g32p_row02_traceSegment_096_1998_0013, g32p_row02_traceSegment_096_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2025 13 14, g32p_row02_traceSegment_096_2025_0013, g32p_row02_traceSegment_096_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1998 27 27, g32p_row02_traceSegment_096_1998_0027, g32p_row02_traceSegment_096_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1944 54 54, g32p_row02_traceSegment_096_1944_0054, g32p_row02_traceSegment_096_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2052 13 14, g32p_row02_traceSegment_096_2052_0013, g32p_row02_traceSegment_096_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2079 13 14, g32p_row02_traceSegment_096_2079_0013, g32p_row02_traceSegment_096_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2052 27 27, g32p_row02_traceSegment_096_2052_0027, g32p_row02_traceSegment_096_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2106 13 14, g32p_row02_traceSegment_096_2106_0013, g32p_row02_traceSegment_096_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2133 13 14, g32p_row02_traceSegment_096_2133_0013, g32p_row02_traceSegment_096_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2106 27 27, g32p_row02_traceSegment_096_2106_0027, g32p_row02_traceSegment_096_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2052 54 54, g32p_row02_traceSegment_096_2052_0054, g32p_row02_traceSegment_096_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1944 108 108, g32p_row02_traceSegment_096_1944_0108, g32p_row02_traceSegment_096_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1728 216 216, g32p_row02_traceSegment_096_1728_0216, g32p_row02_traceSegment_096_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2160 13 14, g32p_row02_traceSegment_096_2160_0013, g32p_row02_traceSegment_096_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2187 13 14, g32p_row02_traceSegment_096_2187_0013, g32p_row02_traceSegment_096_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2160 27 27, g32p_row02_traceSegment_096_2160_0027, g32p_row02_traceSegment_096_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2214 13 14, g32p_row02_traceSegment_096_2214_0013, g32p_row02_traceSegment_096_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2241 13 14, g32p_row02_traceSegment_096_2241_0013, g32p_row02_traceSegment_096_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2214 27 27, g32p_row02_traceSegment_096_2214_0027, g32p_row02_traceSegment_096_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2160 54 54, g32p_row02_traceSegment_096_2160_0054, g32p_row02_traceSegment_096_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2268 13 14, g32p_row02_traceSegment_096_2268_0013, g32p_row02_traceSegment_096_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2295 13 14, g32p_row02_traceSegment_096_2295_0013, g32p_row02_traceSegment_096_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2268 27 27, g32p_row02_traceSegment_096_2268_0027, g32p_row02_traceSegment_096_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2322 13 14, g32p_row02_traceSegment_096_2322_0013, g32p_row02_traceSegment_096_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2349 13 14, g32p_row02_traceSegment_096_2349_0013, g32p_row02_traceSegment_096_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2322 27 27, g32p_row02_traceSegment_096_2322_0027, g32p_row02_traceSegment_096_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2268 54 54, g32p_row02_traceSegment_096_2268_0054, g32p_row02_traceSegment_096_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2160 108 108, g32p_row02_traceSegment_096_2160_0108, g32p_row02_traceSegment_096_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2376 13 14, g32p_row02_traceSegment_096_2376_0013, g32p_row02_traceSegment_096_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2403 13 14, g32p_row02_traceSegment_096_2403_0013, g32p_row02_traceSegment_096_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2376 27 27, g32p_row02_traceSegment_096_2376_0027, g32p_row02_traceSegment_096_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2430 13 14, g32p_row02_traceSegment_096_2430_0013, g32p_row02_traceSegment_096_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2457 13 14, g32p_row02_traceSegment_096_2457_0013, g32p_row02_traceSegment_096_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2430 27 27, g32p_row02_traceSegment_096_2430_0027, g32p_row02_traceSegment_096_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2376 54 54, g32p_row02_traceSegment_096_2376_0054, g32p_row02_traceSegment_096_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2484 13 14, g32p_row02_traceSegment_096_2484_0013, g32p_row02_traceSegment_096_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2511 13 14, g32p_row02_traceSegment_096_2511_0013, g32p_row02_traceSegment_096_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2484 27 27, g32p_row02_traceSegment_096_2484_0027, g32p_row02_traceSegment_096_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2538 13 14, g32p_row02_traceSegment_096_2538_0013, g32p_row02_traceSegment_096_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2565 13 14, g32p_row02_traceSegment_096_2565_0013, g32p_row02_traceSegment_096_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2538 27 27, g32p_row02_traceSegment_096_2538_0027, g32p_row02_traceSegment_096_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2484 54 54, g32p_row02_traceSegment_096_2484_0054, g32p_row02_traceSegment_096_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2376 108 108, g32p_row02_traceSegment_096_2376_0108, g32p_row02_traceSegment_096_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2160 216 216, g32p_row02_traceSegment_096_2160_0216, g32p_row02_traceSegment_096_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1728 432 432, g32p_row02_traceSegment_096_1728_0432, g32p_row02_traceSegment_096_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2592 13 14, g32p_row02_traceSegment_096_2592_0013, g32p_row02_traceSegment_096_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2619 13 14, g32p_row02_traceSegment_096_2619_0013, g32p_row02_traceSegment_096_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2592 27 27, g32p_row02_traceSegment_096_2592_0027, g32p_row02_traceSegment_096_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2646 13 14, g32p_row02_traceSegment_096_2646_0013, g32p_row02_traceSegment_096_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2673 13 14, g32p_row02_traceSegment_096_2673_0013, g32p_row02_traceSegment_096_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2646 27 27, g32p_row02_traceSegment_096_2646_0027, g32p_row02_traceSegment_096_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2592 54 54, g32p_row02_traceSegment_096_2592_0054, g32p_row02_traceSegment_096_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2700 13 14, g32p_row02_traceSegment_096_2700_0013, g32p_row02_traceSegment_096_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2727 13 14, g32p_row02_traceSegment_096_2727_0013, g32p_row02_traceSegment_096_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2700 27 27, g32p_row02_traceSegment_096_2700_0027, g32p_row02_traceSegment_096_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2754 13 14, g32p_row02_traceSegment_096_2754_0013, g32p_row02_traceSegment_096_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2781 13 14, g32p_row02_traceSegment_096_2781_0013, g32p_row02_traceSegment_096_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2754 27 27, g32p_row02_traceSegment_096_2754_0027, g32p_row02_traceSegment_096_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2700 54 54, g32p_row02_traceSegment_096_2700_0054, g32p_row02_traceSegment_096_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2592 108 108, g32p_row02_traceSegment_096_2592_0108, g32p_row02_traceSegment_096_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2808 13 14, g32p_row02_traceSegment_096_2808_0013, g32p_row02_traceSegment_096_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2835 13 14, g32p_row02_traceSegment_096_2835_0013, g32p_row02_traceSegment_096_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2808 27 27, g32p_row02_traceSegment_096_2808_0027, g32p_row02_traceSegment_096_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2862 13 14, g32p_row02_traceSegment_096_2862_0013, g32p_row02_traceSegment_096_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2889 13 14, g32p_row02_traceSegment_096_2889_0013, g32p_row02_traceSegment_096_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2862 27 27, g32p_row02_traceSegment_096_2862_0027, g32p_row02_traceSegment_096_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2808 54 54, g32p_row02_traceSegment_096_2808_0054, g32p_row02_traceSegment_096_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2916 13 14, g32p_row02_traceSegment_096_2916_0013, g32p_row02_traceSegment_096_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2943 13 14, g32p_row02_traceSegment_096_2943_0013, g32p_row02_traceSegment_096_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2916 27 27, g32p_row02_traceSegment_096_2916_0027, g32p_row02_traceSegment_096_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2970 13 14, g32p_row02_traceSegment_096_2970_0013, g32p_row02_traceSegment_096_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2997 13 14, g32p_row02_traceSegment_096_2997_0013, g32p_row02_traceSegment_096_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2970 27 27, g32p_row02_traceSegment_096_2970_0027, g32p_row02_traceSegment_096_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2916 54 54, g32p_row02_traceSegment_096_2916_0054, g32p_row02_traceSegment_096_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2808 108 108, g32p_row02_traceSegment_096_2808_0108, g32p_row02_traceSegment_096_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2592 216 216, g32p_row02_traceSegment_096_2592_0216, g32p_row02_traceSegment_096_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3024 13 14, g32p_row02_traceSegment_096_3024_0013, g32p_row02_traceSegment_096_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3051 13 14, g32p_row02_traceSegment_096_3051_0013, g32p_row02_traceSegment_096_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3024 27 27, g32p_row02_traceSegment_096_3024_0027, g32p_row02_traceSegment_096_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3078 13 14, g32p_row02_traceSegment_096_3078_0013, g32p_row02_traceSegment_096_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3105 13 14, g32p_row02_traceSegment_096_3105_0013, g32p_row02_traceSegment_096_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3078 27 27, g32p_row02_traceSegment_096_3078_0027, g32p_row02_traceSegment_096_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3024 54 54, g32p_row02_traceSegment_096_3024_0054, g32p_row02_traceSegment_096_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3132 13 14, g32p_row02_traceSegment_096_3132_0013, g32p_row02_traceSegment_096_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3159 13 14, g32p_row02_traceSegment_096_3159_0013, g32p_row02_traceSegment_096_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3132 27 27, g32p_row02_traceSegment_096_3132_0027, g32p_row02_traceSegment_096_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3186 13 14, g32p_row02_traceSegment_096_3186_0013, g32p_row02_traceSegment_096_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3213 13 14, g32p_row02_traceSegment_096_3213_0013, g32p_row02_traceSegment_096_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3186 27 27, g32p_row02_traceSegment_096_3186_0027, g32p_row02_traceSegment_096_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3132 54 54, g32p_row02_traceSegment_096_3132_0054, g32p_row02_traceSegment_096_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3024 108 108, g32p_row02_traceSegment_096_3024_0108, g32p_row02_traceSegment_096_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3240 13 14, g32p_row02_traceSegment_096_3240_0013, g32p_row02_traceSegment_096_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3267 13 14, g32p_row02_traceSegment_096_3267_0013, g32p_row02_traceSegment_096_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3240 27 27, g32p_row02_traceSegment_096_3240_0027, g32p_row02_traceSegment_096_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3294 13 14, g32p_row02_traceSegment_096_3294_0013, g32p_row02_traceSegment_096_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3321 13 14, g32p_row02_traceSegment_096_3321_0013, g32p_row02_traceSegment_096_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3294 27 27, g32p_row02_traceSegment_096_3294_0027, g32p_row02_traceSegment_096_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3240 54 54, g32p_row02_traceSegment_096_3240_0054, g32p_row02_traceSegment_096_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3348 13 14, g32p_row02_traceSegment_096_3348_0013, g32p_row02_traceSegment_096_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3375 13 14, g32p_row02_traceSegment_096_3375_0013, g32p_row02_traceSegment_096_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3348 27 27, g32p_row02_traceSegment_096_3348_0027, g32p_row02_traceSegment_096_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3402 13 14, g32p_row02_traceSegment_096_3402_0013, g32p_row02_traceSegment_096_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_096 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_096 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_096_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_096 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3429 13 14, g32p_row02_traceSegment_096_3429_0013, g32p_row02_traceSegment_096_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_096 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3402 27 27, g32p_row02_traceSegment_096_3402_0027, g32p_row02_traceSegment_096_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_096 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3348 54 54, g32p_row02_traceSegment_096_3348_0054, g32p_row02_traceSegment_096_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_096 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3240 108 108, g32p_row02_traceSegment_096_3240_0108, g32p_row02_traceSegment_096_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_096_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_096 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 3024 216 216, g32p_row02_traceSegment_096_3024_0216, g32p_row02_traceSegment_096_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_096_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_096 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 2592 432 432, g32p_row02_traceSegment_096_2592_0432, g32p_row02_traceSegment_096_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_096_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_096 1728 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 1728 864 864, g32p_row02_traceSegment_096_1728_0864, g32p_row02_traceSegment_096_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_096_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_096 0 3456 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_096 0 1728 1728, g32p_row02_traceSegment_096_0000_1728, g32p_row02_traceSegment_096_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 96 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_096_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_097_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 13 14, g32p_row02_traceSegment_097_0000_0013, g32p_row02_traceSegment_097_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 27 13 14, g32p_row02_traceSegment_097_0027_0013, g32p_row02_traceSegment_097_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 27 27, g32p_row02_traceSegment_097_0000_0027, g32p_row02_traceSegment_097_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 67 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 54 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 54 13 14, g32p_row02_traceSegment_097_0054_0013, g32p_row02_traceSegment_097_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 81 13 14, g32p_row02_traceSegment_097_0081_0013, g32p_row02_traceSegment_097_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 54 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 54 27 27, g32p_row02_traceSegment_097_0054_0027, g32p_row02_traceSegment_097_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 54 54, g32p_row02_traceSegment_097_0000_0054, g32p_row02_traceSegment_097_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 108 13 14, g32p_row02_traceSegment_097_0108_0013, g32p_row02_traceSegment_097_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 135 13 14, g32p_row02_traceSegment_097_0135_0013, g32p_row02_traceSegment_097_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 108 27 27, g32p_row02_traceSegment_097_0108_0027, g32p_row02_traceSegment_097_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 162 13 14, g32p_row02_traceSegment_097_0162_0013, g32p_row02_traceSegment_097_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 189 13 14, g32p_row02_traceSegment_097_0189_0013, g32p_row02_traceSegment_097_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 162 27 27, g32p_row02_traceSegment_097_0162_0027, g32p_row02_traceSegment_097_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 108 54 54, g32p_row02_traceSegment_097_0108_0054, g32p_row02_traceSegment_097_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 0 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 108 108, g32p_row02_traceSegment_097_0000_0108, g32p_row02_traceSegment_097_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 216 13 14, g32p_row02_traceSegment_097_0216_0013, g32p_row02_traceSegment_097_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 243 13 14, g32p_row02_traceSegment_097_0243_0013, g32p_row02_traceSegment_097_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 216 27 27, g32p_row02_traceSegment_097_0216_0027, g32p_row02_traceSegment_097_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 270 13 14, g32p_row02_traceSegment_097_0270_0013, g32p_row02_traceSegment_097_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 297 13 14, g32p_row02_traceSegment_097_0297_0013, g32p_row02_traceSegment_097_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 270 27 27, g32p_row02_traceSegment_097_0270_0027, g32p_row02_traceSegment_097_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 216 54 54, g32p_row02_traceSegment_097_0216_0054, g32p_row02_traceSegment_097_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 324 13 14, g32p_row02_traceSegment_097_0324_0013, g32p_row02_traceSegment_097_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 351 13 14, g32p_row02_traceSegment_097_0351_0013, g32p_row02_traceSegment_097_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 324 27 27, g32p_row02_traceSegment_097_0324_0027, g32p_row02_traceSegment_097_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 378 13 14, g32p_row02_traceSegment_097_0378_0013, g32p_row02_traceSegment_097_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 405 13 14, g32p_row02_traceSegment_097_0405_0013, g32p_row02_traceSegment_097_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 378 27 27, g32p_row02_traceSegment_097_0378_0027, g32p_row02_traceSegment_097_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 324 54 54, g32p_row02_traceSegment_097_0324_0054, g32p_row02_traceSegment_097_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 216 108 108, g32p_row02_traceSegment_097_0216_0108, g32p_row02_traceSegment_097_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 0 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 216 216, g32p_row02_traceSegment_097_0000_0216, g32p_row02_traceSegment_097_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 432 13 14, g32p_row02_traceSegment_097_0432_0013, g32p_row02_traceSegment_097_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 459 13 14, g32p_row02_traceSegment_097_0459_0013, g32p_row02_traceSegment_097_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 432 27 27, g32p_row02_traceSegment_097_0432_0027, g32p_row02_traceSegment_097_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 486 13 14, g32p_row02_traceSegment_097_0486_0013, g32p_row02_traceSegment_097_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 513 13 14, g32p_row02_traceSegment_097_0513_0013, g32p_row02_traceSegment_097_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 486 27 27, g32p_row02_traceSegment_097_0486_0027, g32p_row02_traceSegment_097_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 432 54 54, g32p_row02_traceSegment_097_0432_0054, g32p_row02_traceSegment_097_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 540 13 14, g32p_row02_traceSegment_097_0540_0013, g32p_row02_traceSegment_097_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 567 13 14, g32p_row02_traceSegment_097_0567_0013, g32p_row02_traceSegment_097_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 540 27 27, g32p_row02_traceSegment_097_0540_0027, g32p_row02_traceSegment_097_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 594 13 14, g32p_row02_traceSegment_097_0594_0013, g32p_row02_traceSegment_097_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 621 13 14, g32p_row02_traceSegment_097_0621_0013, g32p_row02_traceSegment_097_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 594 27 27, g32p_row02_traceSegment_097_0594_0027, g32p_row02_traceSegment_097_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 540 54 54, g32p_row02_traceSegment_097_0540_0054, g32p_row02_traceSegment_097_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 432 108 108, g32p_row02_traceSegment_097_0432_0108, g32p_row02_traceSegment_097_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 648 13 14, g32p_row02_traceSegment_097_0648_0013, g32p_row02_traceSegment_097_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 675 13 14, g32p_row02_traceSegment_097_0675_0013, g32p_row02_traceSegment_097_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 648 27 27, g32p_row02_traceSegment_097_0648_0027, g32p_row02_traceSegment_097_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 702 13 14, g32p_row02_traceSegment_097_0702_0013, g32p_row02_traceSegment_097_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 729 13 14, g32p_row02_traceSegment_097_0729_0013, g32p_row02_traceSegment_097_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 702 27 27, g32p_row02_traceSegment_097_0702_0027, g32p_row02_traceSegment_097_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 648 54 54, g32p_row02_traceSegment_097_0648_0054, g32p_row02_traceSegment_097_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 756 13 14, g32p_row02_traceSegment_097_0756_0013, g32p_row02_traceSegment_097_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 783 13 14, g32p_row02_traceSegment_097_0783_0013, g32p_row02_traceSegment_097_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 756 27 27, g32p_row02_traceSegment_097_0756_0027, g32p_row02_traceSegment_097_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 810 13 14, g32p_row02_traceSegment_097_0810_0013, g32p_row02_traceSegment_097_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 837 13 14, g32p_row02_traceSegment_097_0837_0013, g32p_row02_traceSegment_097_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 810 27 27, g32p_row02_traceSegment_097_0810_0027, g32p_row02_traceSegment_097_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 756 54 54, g32p_row02_traceSegment_097_0756_0054, g32p_row02_traceSegment_097_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 648 108 108, g32p_row02_traceSegment_097_0648_0108, g32p_row02_traceSegment_097_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 432 216 216, g32p_row02_traceSegment_097_0432_0216, g32p_row02_traceSegment_097_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_097 0 864 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 432 432, g32p_row02_traceSegment_097_0000_0432, g32p_row02_traceSegment_097_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 864 13 14, g32p_row02_traceSegment_097_0864_0013, g32p_row02_traceSegment_097_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 891 13 14, g32p_row02_traceSegment_097_0891_0013, g32p_row02_traceSegment_097_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 864 27 27, g32p_row02_traceSegment_097_0864_0027, g32p_row02_traceSegment_097_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 918 13 14, g32p_row02_traceSegment_097_0918_0013, g32p_row02_traceSegment_097_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 945 13 14, g32p_row02_traceSegment_097_0945_0013, g32p_row02_traceSegment_097_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 918 27 27, g32p_row02_traceSegment_097_0918_0027, g32p_row02_traceSegment_097_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 864 54 54, g32p_row02_traceSegment_097_0864_0054, g32p_row02_traceSegment_097_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 972 13 14, g32p_row02_traceSegment_097_0972_0013, g32p_row02_traceSegment_097_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 999 13 14, g32p_row02_traceSegment_097_0999_0013, g32p_row02_traceSegment_097_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 972 27 27, g32p_row02_traceSegment_097_0972_0027, g32p_row02_traceSegment_097_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1026 13 14, g32p_row02_traceSegment_097_1026_0013, g32p_row02_traceSegment_097_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1053 13 14, g32p_row02_traceSegment_097_1053_0013, g32p_row02_traceSegment_097_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1026 27 27, g32p_row02_traceSegment_097_1026_0027, g32p_row02_traceSegment_097_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 972 54 54, g32p_row02_traceSegment_097_0972_0054, g32p_row02_traceSegment_097_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 864 108 108, g32p_row02_traceSegment_097_0864_0108, g32p_row02_traceSegment_097_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1080 13 14, g32p_row02_traceSegment_097_1080_0013, g32p_row02_traceSegment_097_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1107 13 14, g32p_row02_traceSegment_097_1107_0013, g32p_row02_traceSegment_097_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1080 27 27, g32p_row02_traceSegment_097_1080_0027, g32p_row02_traceSegment_097_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1134 13 14, g32p_row02_traceSegment_097_1134_0013, g32p_row02_traceSegment_097_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1161 13 14, g32p_row02_traceSegment_097_1161_0013, g32p_row02_traceSegment_097_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1134 27 27, g32p_row02_traceSegment_097_1134_0027, g32p_row02_traceSegment_097_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1080 54 54, g32p_row02_traceSegment_097_1080_0054, g32p_row02_traceSegment_097_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1188 13 14, g32p_row02_traceSegment_097_1188_0013, g32p_row02_traceSegment_097_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1215 13 14, g32p_row02_traceSegment_097_1215_0013, g32p_row02_traceSegment_097_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1188 27 27, g32p_row02_traceSegment_097_1188_0027, g32p_row02_traceSegment_097_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1242 13 14, g32p_row02_traceSegment_097_1242_0013, g32p_row02_traceSegment_097_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1269 13 14, g32p_row02_traceSegment_097_1269_0013, g32p_row02_traceSegment_097_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1242 27 27, g32p_row02_traceSegment_097_1242_0027, g32p_row02_traceSegment_097_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1188 54 54, g32p_row02_traceSegment_097_1188_0054, g32p_row02_traceSegment_097_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1080 108 108, g32p_row02_traceSegment_097_1080_0108, g32p_row02_traceSegment_097_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 864 216 216, g32p_row02_traceSegment_097_0864_0216, g32p_row02_traceSegment_097_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1296 13 14, g32p_row02_traceSegment_097_1296_0013, g32p_row02_traceSegment_097_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1323 13 14, g32p_row02_traceSegment_097_1323_0013, g32p_row02_traceSegment_097_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1296 27 27, g32p_row02_traceSegment_097_1296_0027, g32p_row02_traceSegment_097_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1350 13 14, g32p_row02_traceSegment_097_1350_0013, g32p_row02_traceSegment_097_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1377 13 14, g32p_row02_traceSegment_097_1377_0013, g32p_row02_traceSegment_097_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1350 27 27, g32p_row02_traceSegment_097_1350_0027, g32p_row02_traceSegment_097_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1296 54 54, g32p_row02_traceSegment_097_1296_0054, g32p_row02_traceSegment_097_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1404 13 14, g32p_row02_traceSegment_097_1404_0013, g32p_row02_traceSegment_097_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1431 13 14, g32p_row02_traceSegment_097_1431_0013, g32p_row02_traceSegment_097_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1404 27 27, g32p_row02_traceSegment_097_1404_0027, g32p_row02_traceSegment_097_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1458 13 14, g32p_row02_traceSegment_097_1458_0013, g32p_row02_traceSegment_097_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1485 13 14, g32p_row02_traceSegment_097_1485_0013, g32p_row02_traceSegment_097_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1458 27 27, g32p_row02_traceSegment_097_1458_0027, g32p_row02_traceSegment_097_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1404 54 54, g32p_row02_traceSegment_097_1404_0054, g32p_row02_traceSegment_097_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1296 108 108, g32p_row02_traceSegment_097_1296_0108, g32p_row02_traceSegment_097_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1512 13 14, g32p_row02_traceSegment_097_1512_0013, g32p_row02_traceSegment_097_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1539 13 14, g32p_row02_traceSegment_097_1539_0013, g32p_row02_traceSegment_097_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1512 27 27, g32p_row02_traceSegment_097_1512_0027, g32p_row02_traceSegment_097_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1566 13 14, g32p_row02_traceSegment_097_1566_0013, g32p_row02_traceSegment_097_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1593 13 14, g32p_row02_traceSegment_097_1593_0013, g32p_row02_traceSegment_097_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1566 27 27, g32p_row02_traceSegment_097_1566_0027, g32p_row02_traceSegment_097_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1512 54 54, g32p_row02_traceSegment_097_1512_0054, g32p_row02_traceSegment_097_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1620 13 14, g32p_row02_traceSegment_097_1620_0013, g32p_row02_traceSegment_097_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1647 13 14, g32p_row02_traceSegment_097_1647_0013, g32p_row02_traceSegment_097_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1620 27 27, g32p_row02_traceSegment_097_1620_0027, g32p_row02_traceSegment_097_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1674 13 14, g32p_row02_traceSegment_097_1674_0013, g32p_row02_traceSegment_097_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1701 13 14, g32p_row02_traceSegment_097_1701_0013, g32p_row02_traceSegment_097_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1674 27 27, g32p_row02_traceSegment_097_1674_0027, g32p_row02_traceSegment_097_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1620 54 54, g32p_row02_traceSegment_097_1620_0054, g32p_row02_traceSegment_097_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1512 108 108, g32p_row02_traceSegment_097_1512_0108, g32p_row02_traceSegment_097_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1296 216 216, g32p_row02_traceSegment_097_1296_0216, g32p_row02_traceSegment_097_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_097 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 864 432 432, g32p_row02_traceSegment_097_0864_0432, g32p_row02_traceSegment_097_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_097 0 1728 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 864 864, g32p_row02_traceSegment_097_0000_0864, g32p_row02_traceSegment_097_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1728 13 14, g32p_row02_traceSegment_097_1728_0013, g32p_row02_traceSegment_097_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1755 13 14, g32p_row02_traceSegment_097_1755_0013, g32p_row02_traceSegment_097_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1728 27 27, g32p_row02_traceSegment_097_1728_0027, g32p_row02_traceSegment_097_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1782 13 14, g32p_row02_traceSegment_097_1782_0013, g32p_row02_traceSegment_097_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1809 13 14, g32p_row02_traceSegment_097_1809_0013, g32p_row02_traceSegment_097_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1782 27 27, g32p_row02_traceSegment_097_1782_0027, g32p_row02_traceSegment_097_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1728 54 54, g32p_row02_traceSegment_097_1728_0054, g32p_row02_traceSegment_097_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1836 13 14, g32p_row02_traceSegment_097_1836_0013, g32p_row02_traceSegment_097_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1863 13 14, g32p_row02_traceSegment_097_1863_0013, g32p_row02_traceSegment_097_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1836 27 27, g32p_row02_traceSegment_097_1836_0027, g32p_row02_traceSegment_097_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1890 13 14, g32p_row02_traceSegment_097_1890_0013, g32p_row02_traceSegment_097_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1917 13 14, g32p_row02_traceSegment_097_1917_0013, g32p_row02_traceSegment_097_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1890 27 27, g32p_row02_traceSegment_097_1890_0027, g32p_row02_traceSegment_097_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1836 54 54, g32p_row02_traceSegment_097_1836_0054, g32p_row02_traceSegment_097_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1728 108 108, g32p_row02_traceSegment_097_1728_0108, g32p_row02_traceSegment_097_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1944 13 14, g32p_row02_traceSegment_097_1944_0013, g32p_row02_traceSegment_097_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1971 13 14, g32p_row02_traceSegment_097_1971_0013, g32p_row02_traceSegment_097_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1944 27 27, g32p_row02_traceSegment_097_1944_0027, g32p_row02_traceSegment_097_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1998 13 14, g32p_row02_traceSegment_097_1998_0013, g32p_row02_traceSegment_097_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2025 13 14, g32p_row02_traceSegment_097_2025_0013, g32p_row02_traceSegment_097_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1998 27 27, g32p_row02_traceSegment_097_1998_0027, g32p_row02_traceSegment_097_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1944 54 54, g32p_row02_traceSegment_097_1944_0054, g32p_row02_traceSegment_097_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2052 13 14, g32p_row02_traceSegment_097_2052_0013, g32p_row02_traceSegment_097_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2079 13 14, g32p_row02_traceSegment_097_2079_0013, g32p_row02_traceSegment_097_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2052 27 27, g32p_row02_traceSegment_097_2052_0027, g32p_row02_traceSegment_097_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2106 13 14, g32p_row02_traceSegment_097_2106_0013, g32p_row02_traceSegment_097_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2133 13 14, g32p_row02_traceSegment_097_2133_0013, g32p_row02_traceSegment_097_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2106 27 27, g32p_row02_traceSegment_097_2106_0027, g32p_row02_traceSegment_097_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2052 54 54, g32p_row02_traceSegment_097_2052_0054, g32p_row02_traceSegment_097_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1944 108 108, g32p_row02_traceSegment_097_1944_0108, g32p_row02_traceSegment_097_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1728 216 216, g32p_row02_traceSegment_097_1728_0216, g32p_row02_traceSegment_097_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2160 13 14, g32p_row02_traceSegment_097_2160_0013, g32p_row02_traceSegment_097_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2187 13 14, g32p_row02_traceSegment_097_2187_0013, g32p_row02_traceSegment_097_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2160 27 27, g32p_row02_traceSegment_097_2160_0027, g32p_row02_traceSegment_097_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2214 13 14, g32p_row02_traceSegment_097_2214_0013, g32p_row02_traceSegment_097_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2241 13 14, g32p_row02_traceSegment_097_2241_0013, g32p_row02_traceSegment_097_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2214 27 27, g32p_row02_traceSegment_097_2214_0027, g32p_row02_traceSegment_097_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2160 54 54, g32p_row02_traceSegment_097_2160_0054, g32p_row02_traceSegment_097_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2268 13 14, g32p_row02_traceSegment_097_2268_0013, g32p_row02_traceSegment_097_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2295 13 14, g32p_row02_traceSegment_097_2295_0013, g32p_row02_traceSegment_097_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2268 27 27, g32p_row02_traceSegment_097_2268_0027, g32p_row02_traceSegment_097_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2322 13 14, g32p_row02_traceSegment_097_2322_0013, g32p_row02_traceSegment_097_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2349 13 14, g32p_row02_traceSegment_097_2349_0013, g32p_row02_traceSegment_097_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2322 27 27, g32p_row02_traceSegment_097_2322_0027, g32p_row02_traceSegment_097_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2268 54 54, g32p_row02_traceSegment_097_2268_0054, g32p_row02_traceSegment_097_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2160 108 108, g32p_row02_traceSegment_097_2160_0108, g32p_row02_traceSegment_097_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2376 13 14, g32p_row02_traceSegment_097_2376_0013, g32p_row02_traceSegment_097_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2403 13 14, g32p_row02_traceSegment_097_2403_0013, g32p_row02_traceSegment_097_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2376 27 27, g32p_row02_traceSegment_097_2376_0027, g32p_row02_traceSegment_097_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2430 13 14, g32p_row02_traceSegment_097_2430_0013, g32p_row02_traceSegment_097_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2457 13 14, g32p_row02_traceSegment_097_2457_0013, g32p_row02_traceSegment_097_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2430 27 27, g32p_row02_traceSegment_097_2430_0027, g32p_row02_traceSegment_097_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2376 54 54, g32p_row02_traceSegment_097_2376_0054, g32p_row02_traceSegment_097_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2484 13 14, g32p_row02_traceSegment_097_2484_0013, g32p_row02_traceSegment_097_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2511 13 14, g32p_row02_traceSegment_097_2511_0013, g32p_row02_traceSegment_097_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2484 27 27, g32p_row02_traceSegment_097_2484_0027, g32p_row02_traceSegment_097_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2538 13 14, g32p_row02_traceSegment_097_2538_0013, g32p_row02_traceSegment_097_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2565 13 14, g32p_row02_traceSegment_097_2565_0013, g32p_row02_traceSegment_097_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2538 27 27, g32p_row02_traceSegment_097_2538_0027, g32p_row02_traceSegment_097_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2484 54 54, g32p_row02_traceSegment_097_2484_0054, g32p_row02_traceSegment_097_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2376 108 108, g32p_row02_traceSegment_097_2376_0108, g32p_row02_traceSegment_097_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2160 216 216, g32p_row02_traceSegment_097_2160_0216, g32p_row02_traceSegment_097_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1728 432 432, g32p_row02_traceSegment_097_1728_0432, g32p_row02_traceSegment_097_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2592 13 14, g32p_row02_traceSegment_097_2592_0013, g32p_row02_traceSegment_097_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2619 13 14, g32p_row02_traceSegment_097_2619_0013, g32p_row02_traceSegment_097_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2592 27 27, g32p_row02_traceSegment_097_2592_0027, g32p_row02_traceSegment_097_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2646 13 14, g32p_row02_traceSegment_097_2646_0013, g32p_row02_traceSegment_097_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2673 13 14, g32p_row02_traceSegment_097_2673_0013, g32p_row02_traceSegment_097_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2646 27 27, g32p_row02_traceSegment_097_2646_0027, g32p_row02_traceSegment_097_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2592 54 54, g32p_row02_traceSegment_097_2592_0054, g32p_row02_traceSegment_097_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2700 13 14, g32p_row02_traceSegment_097_2700_0013, g32p_row02_traceSegment_097_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2727 13 14, g32p_row02_traceSegment_097_2727_0013, g32p_row02_traceSegment_097_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2700 27 27, g32p_row02_traceSegment_097_2700_0027, g32p_row02_traceSegment_097_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2754 13 14, g32p_row02_traceSegment_097_2754_0013, g32p_row02_traceSegment_097_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2781 13 14, g32p_row02_traceSegment_097_2781_0013, g32p_row02_traceSegment_097_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2754 27 27, g32p_row02_traceSegment_097_2754_0027, g32p_row02_traceSegment_097_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2700 54 54, g32p_row02_traceSegment_097_2700_0054, g32p_row02_traceSegment_097_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2592 108 108, g32p_row02_traceSegment_097_2592_0108, g32p_row02_traceSegment_097_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2808 13 14, g32p_row02_traceSegment_097_2808_0013, g32p_row02_traceSegment_097_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2835 13 14, g32p_row02_traceSegment_097_2835_0013, g32p_row02_traceSegment_097_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2808 27 27, g32p_row02_traceSegment_097_2808_0027, g32p_row02_traceSegment_097_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2862 13 14, g32p_row02_traceSegment_097_2862_0013, g32p_row02_traceSegment_097_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2889 13 14, g32p_row02_traceSegment_097_2889_0013, g32p_row02_traceSegment_097_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2862 27 27, g32p_row02_traceSegment_097_2862_0027, g32p_row02_traceSegment_097_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2808 54 54, g32p_row02_traceSegment_097_2808_0054, g32p_row02_traceSegment_097_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2916 13 14, g32p_row02_traceSegment_097_2916_0013, g32p_row02_traceSegment_097_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2943 13 14, g32p_row02_traceSegment_097_2943_0013, g32p_row02_traceSegment_097_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2916 27 27, g32p_row02_traceSegment_097_2916_0027, g32p_row02_traceSegment_097_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2970 13 14, g32p_row02_traceSegment_097_2970_0013, g32p_row02_traceSegment_097_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2997 13 14, g32p_row02_traceSegment_097_2997_0013, g32p_row02_traceSegment_097_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2970 27 27, g32p_row02_traceSegment_097_2970_0027, g32p_row02_traceSegment_097_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2916 54 54, g32p_row02_traceSegment_097_2916_0054, g32p_row02_traceSegment_097_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2808 108 108, g32p_row02_traceSegment_097_2808_0108, g32p_row02_traceSegment_097_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2592 216 216, g32p_row02_traceSegment_097_2592_0216, g32p_row02_traceSegment_097_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3024 13 14, g32p_row02_traceSegment_097_3024_0013, g32p_row02_traceSegment_097_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3051 13 14, g32p_row02_traceSegment_097_3051_0013, g32p_row02_traceSegment_097_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3024 27 27, g32p_row02_traceSegment_097_3024_0027, g32p_row02_traceSegment_097_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3078 13 14, g32p_row02_traceSegment_097_3078_0013, g32p_row02_traceSegment_097_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3105 13 14, g32p_row02_traceSegment_097_3105_0013, g32p_row02_traceSegment_097_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3078 27 27, g32p_row02_traceSegment_097_3078_0027, g32p_row02_traceSegment_097_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3024 54 54, g32p_row02_traceSegment_097_3024_0054, g32p_row02_traceSegment_097_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3132 13 14, g32p_row02_traceSegment_097_3132_0013, g32p_row02_traceSegment_097_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3159 13 14, g32p_row02_traceSegment_097_3159_0013, g32p_row02_traceSegment_097_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3132 27 27, g32p_row02_traceSegment_097_3132_0027, g32p_row02_traceSegment_097_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3186 13 14, g32p_row02_traceSegment_097_3186_0013, g32p_row02_traceSegment_097_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3213 13 14, g32p_row02_traceSegment_097_3213_0013, g32p_row02_traceSegment_097_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3186 27 27, g32p_row02_traceSegment_097_3186_0027, g32p_row02_traceSegment_097_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3132 54 54, g32p_row02_traceSegment_097_3132_0054, g32p_row02_traceSegment_097_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3024 108 108, g32p_row02_traceSegment_097_3024_0108, g32p_row02_traceSegment_097_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3240 13 14, g32p_row02_traceSegment_097_3240_0013, g32p_row02_traceSegment_097_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3267 13 14, g32p_row02_traceSegment_097_3267_0013, g32p_row02_traceSegment_097_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3240 27 27, g32p_row02_traceSegment_097_3240_0027, g32p_row02_traceSegment_097_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3294 13 14, g32p_row02_traceSegment_097_3294_0013, g32p_row02_traceSegment_097_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3321 13 14, g32p_row02_traceSegment_097_3321_0013, g32p_row02_traceSegment_097_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3294 27 27, g32p_row02_traceSegment_097_3294_0027, g32p_row02_traceSegment_097_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3240 54 54, g32p_row02_traceSegment_097_3240_0054, g32p_row02_traceSegment_097_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3348 13 14, g32p_row02_traceSegment_097_3348_0013, g32p_row02_traceSegment_097_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3375 13 14, g32p_row02_traceSegment_097_3375_0013, g32p_row02_traceSegment_097_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3348 27 27, g32p_row02_traceSegment_097_3348_0027, g32p_row02_traceSegment_097_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3402 13 14, g32p_row02_traceSegment_097_3402_0013, g32p_row02_traceSegment_097_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_097 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_097 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_097_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_097 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3429 13 14, g32p_row02_traceSegment_097_3429_0013, g32p_row02_traceSegment_097_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_097 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3402 27 27, g32p_row02_traceSegment_097_3402_0027, g32p_row02_traceSegment_097_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_097 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3348 54 54, g32p_row02_traceSegment_097_3348_0054, g32p_row02_traceSegment_097_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_097 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3240 108 108, g32p_row02_traceSegment_097_3240_0108, g32p_row02_traceSegment_097_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_097_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_097 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 3024 216 216, g32p_row02_traceSegment_097_3024_0216, g32p_row02_traceSegment_097_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_097_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_097 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 2592 432 432, g32p_row02_traceSegment_097_2592_0432, g32p_row02_traceSegment_097_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_097_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_097 1728 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 1728 864 864, g32p_row02_traceSegment_097_1728_0864, g32p_row02_traceSegment_097_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_097_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_097 0 3456 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_097 0 1728 1728, g32p_row02_traceSegment_097_0000_1728, g32p_row02_traceSegment_097_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 97 = [0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_097_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 90) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 90) (g32p_literalTraceValue 1 90)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_090]
  decide +kernel

theorem g32p_row02_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 91) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 91) (g32p_literalTraceValue 1 91)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_091]
  decide +kernel

theorem g32p_row02_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 92) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 92) (g32p_literalTraceValue 1 92)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_092]
  decide +kernel

theorem g32p_row02_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 93) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 93) (g32p_literalTraceValue 1 93)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_093]
  decide +kernel

theorem g32p_row02_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 94) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 94) (g32p_literalTraceValue 1 94)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_094]
  decide +kernel

theorem g32p_row02_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 95) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 95) (g32p_literalTraceValue 1 95)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_095]
  decide +kernel

theorem g32p_row02_tracePolynomial_096 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 96) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 96) (g32p_literalTraceValue 1 96)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_096]
  decide +kernel

theorem g32p_row02_tracePolynomial_097 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 97) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 97) (g32p_literalTraceValue 1 97)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_097]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
