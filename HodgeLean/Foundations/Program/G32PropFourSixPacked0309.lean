import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0308

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_086 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 86 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_086_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 13 14, g32p_row02_traceSegment_086_0000_0013, g32p_row02_traceSegment_086_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 27 13 14, g32p_row02_traceSegment_086_0027_0013, g32p_row02_traceSegment_086_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 27 27, g32p_row02_traceSegment_086_0000_0027, g32p_row02_traceSegment_086_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 54 13 14, g32p_row02_traceSegment_086_0054_0013, g32p_row02_traceSegment_086_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 81 13 14, g32p_row02_traceSegment_086_0081_0013, g32p_row02_traceSegment_086_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 54 27 27, g32p_row02_traceSegment_086_0054_0027, g32p_row02_traceSegment_086_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 54 54, g32p_row02_traceSegment_086_0000_0054, g32p_row02_traceSegment_086_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 108 13 14, g32p_row02_traceSegment_086_0108_0013, g32p_row02_traceSegment_086_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 135 13 14, g32p_row02_traceSegment_086_0135_0013, g32p_row02_traceSegment_086_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 108 27 27, g32p_row02_traceSegment_086_0108_0027, g32p_row02_traceSegment_086_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 162 13 14, g32p_row02_traceSegment_086_0162_0013, g32p_row02_traceSegment_086_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 189 13 14, g32p_row02_traceSegment_086_0189_0013, g32p_row02_traceSegment_086_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 162 27 27, g32p_row02_traceSegment_086_0162_0027, g32p_row02_traceSegment_086_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 108 54 54, g32p_row02_traceSegment_086_0108_0054, g32p_row02_traceSegment_086_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 108 108, g32p_row02_traceSegment_086_0000_0108, g32p_row02_traceSegment_086_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 216 13 14, g32p_row02_traceSegment_086_0216_0013, g32p_row02_traceSegment_086_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 243 13 14, g32p_row02_traceSegment_086_0243_0013, g32p_row02_traceSegment_086_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 216 27 27, g32p_row02_traceSegment_086_0216_0027, g32p_row02_traceSegment_086_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 270 13 14, g32p_row02_traceSegment_086_0270_0013, g32p_row02_traceSegment_086_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 297 13 14, g32p_row02_traceSegment_086_0297_0013, g32p_row02_traceSegment_086_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 270 27 27, g32p_row02_traceSegment_086_0270_0027, g32p_row02_traceSegment_086_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 216 54 54, g32p_row02_traceSegment_086_0216_0054, g32p_row02_traceSegment_086_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 324 13 14, g32p_row02_traceSegment_086_0324_0013, g32p_row02_traceSegment_086_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 351 13 14, g32p_row02_traceSegment_086_0351_0013, g32p_row02_traceSegment_086_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 324 27 27, g32p_row02_traceSegment_086_0324_0027, g32p_row02_traceSegment_086_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 378 13 14, g32p_row02_traceSegment_086_0378_0013, g32p_row02_traceSegment_086_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 405 13 14, g32p_row02_traceSegment_086_0405_0013, g32p_row02_traceSegment_086_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 378 27 27, g32p_row02_traceSegment_086_0378_0027, g32p_row02_traceSegment_086_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 324 54 54, g32p_row02_traceSegment_086_0324_0054, g32p_row02_traceSegment_086_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 216 108 108, g32p_row02_traceSegment_086_0216_0108, g32p_row02_traceSegment_086_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 216 216, g32p_row02_traceSegment_086_0000_0216, g32p_row02_traceSegment_086_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 432 13 14, g32p_row02_traceSegment_086_0432_0013, g32p_row02_traceSegment_086_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 459 13 14, g32p_row02_traceSegment_086_0459_0013, g32p_row02_traceSegment_086_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 432 27 27, g32p_row02_traceSegment_086_0432_0027, g32p_row02_traceSegment_086_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 486 13 14, g32p_row02_traceSegment_086_0486_0013, g32p_row02_traceSegment_086_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 513 13 14, g32p_row02_traceSegment_086_0513_0013, g32p_row02_traceSegment_086_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 486 27 27, g32p_row02_traceSegment_086_0486_0027, g32p_row02_traceSegment_086_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 432 54 54, g32p_row02_traceSegment_086_0432_0054, g32p_row02_traceSegment_086_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 540 13 14, g32p_row02_traceSegment_086_0540_0013, g32p_row02_traceSegment_086_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 567 13 14, g32p_row02_traceSegment_086_0567_0013, g32p_row02_traceSegment_086_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 540 27 27, g32p_row02_traceSegment_086_0540_0027, g32p_row02_traceSegment_086_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 594 13 14, g32p_row02_traceSegment_086_0594_0013, g32p_row02_traceSegment_086_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 621 13 14, g32p_row02_traceSegment_086_0621_0013, g32p_row02_traceSegment_086_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 594 27 27, g32p_row02_traceSegment_086_0594_0027, g32p_row02_traceSegment_086_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 540 54 54, g32p_row02_traceSegment_086_0540_0054, g32p_row02_traceSegment_086_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 432 108 108, g32p_row02_traceSegment_086_0432_0108, g32p_row02_traceSegment_086_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 648 13 14, g32p_row02_traceSegment_086_0648_0013, g32p_row02_traceSegment_086_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 675 13 14, g32p_row02_traceSegment_086_0675_0013, g32p_row02_traceSegment_086_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 648 27 27, g32p_row02_traceSegment_086_0648_0027, g32p_row02_traceSegment_086_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 702 13 14, g32p_row02_traceSegment_086_0702_0013, g32p_row02_traceSegment_086_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 729 13 14, g32p_row02_traceSegment_086_0729_0013, g32p_row02_traceSegment_086_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 702 27 27, g32p_row02_traceSegment_086_0702_0027, g32p_row02_traceSegment_086_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 648 54 54, g32p_row02_traceSegment_086_0648_0054, g32p_row02_traceSegment_086_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 756 13 14, g32p_row02_traceSegment_086_0756_0013, g32p_row02_traceSegment_086_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 783 13 14, g32p_row02_traceSegment_086_0783_0013, g32p_row02_traceSegment_086_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 756 27 27, g32p_row02_traceSegment_086_0756_0027, g32p_row02_traceSegment_086_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 810 13 14, g32p_row02_traceSegment_086_0810_0013, g32p_row02_traceSegment_086_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 837 13 14, g32p_row02_traceSegment_086_0837_0013, g32p_row02_traceSegment_086_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 810 27 27, g32p_row02_traceSegment_086_0810_0027, g32p_row02_traceSegment_086_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 756 54 54, g32p_row02_traceSegment_086_0756_0054, g32p_row02_traceSegment_086_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 648 108 108, g32p_row02_traceSegment_086_0648_0108, g32p_row02_traceSegment_086_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 432 216 216, g32p_row02_traceSegment_086_0432_0216, g32p_row02_traceSegment_086_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_086 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 432 432, g32p_row02_traceSegment_086_0000_0432, g32p_row02_traceSegment_086_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 864 13 14, g32p_row02_traceSegment_086_0864_0013, g32p_row02_traceSegment_086_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 891 13 14, g32p_row02_traceSegment_086_0891_0013, g32p_row02_traceSegment_086_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 864 27 27, g32p_row02_traceSegment_086_0864_0027, g32p_row02_traceSegment_086_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 918 13 14, g32p_row02_traceSegment_086_0918_0013, g32p_row02_traceSegment_086_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 958 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 945 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 945 13 14, g32p_row02_traceSegment_086_0945_0013, g32p_row02_traceSegment_086_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 918 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 918 27 27, g32p_row02_traceSegment_086_0918_0027, g32p_row02_traceSegment_086_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 864 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 864 54 54, g32p_row02_traceSegment_086_0864_0054, g32p_row02_traceSegment_086_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 972 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 972 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 972 13 14, g32p_row02_traceSegment_086_0972_0013, g32p_row02_traceSegment_086_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 999 13 14, g32p_row02_traceSegment_086_0999_0013, g32p_row02_traceSegment_086_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 972 27 27, g32p_row02_traceSegment_086_0972_0027, g32p_row02_traceSegment_086_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1026 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1026 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1026 13 14, g32p_row02_traceSegment_086_1026_0013, g32p_row02_traceSegment_086_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1066 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1053 13 14, g32p_row02_traceSegment_086_1053_0013, g32p_row02_traceSegment_086_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1026 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1026 27 27, g32p_row02_traceSegment_086_1026_0027, g32p_row02_traceSegment_086_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 972 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 972 54 54, g32p_row02_traceSegment_086_0972_0054, g32p_row02_traceSegment_086_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 864 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 864 108 108, g32p_row02_traceSegment_086_0864_0108, g32p_row02_traceSegment_086_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1080 13 14, g32p_row02_traceSegment_086_1080_0013, g32p_row02_traceSegment_086_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1107 13 14, g32p_row02_traceSegment_086_1107_0013, g32p_row02_traceSegment_086_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1080 27 27, g32p_row02_traceSegment_086_1080_0027, g32p_row02_traceSegment_086_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1134 13 14, g32p_row02_traceSegment_086_1134_0013, g32p_row02_traceSegment_086_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1174 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1161 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1161 13 14, g32p_row02_traceSegment_086_1161_0013, g32p_row02_traceSegment_086_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1134 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1134 27 27, g32p_row02_traceSegment_086_1134_0027, g32p_row02_traceSegment_086_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1080 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1080 54 54, g32p_row02_traceSegment_086_1080_0054, g32p_row02_traceSegment_086_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1188 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1188 13 14, g32p_row02_traceSegment_086_1188_0013, g32p_row02_traceSegment_086_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1228 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1215 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1215 13 14, g32p_row02_traceSegment_086_1215_0013, g32p_row02_traceSegment_086_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1188 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1188 27 27, g32p_row02_traceSegment_086_1188_0027, g32p_row02_traceSegment_086_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1255 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1242 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1242 13 14, g32p_row02_traceSegment_086_1242_0013, g32p_row02_traceSegment_086_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1269 13 14, g32p_row02_traceSegment_086_1269_0013, g32p_row02_traceSegment_086_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1242 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1242 27 27, g32p_row02_traceSegment_086_1242_0027, g32p_row02_traceSegment_086_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1188 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1188 54 54, g32p_row02_traceSegment_086_1188_0054, g32p_row02_traceSegment_086_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 1080 216 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1080 108 108, g32p_row02_traceSegment_086_1080_0108, g32p_row02_traceSegment_086_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 864 432 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 864 216 216, g32p_row02_traceSegment_086_0864_0216, g32p_row02_traceSegment_086_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1309 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1296 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1296 13 14, g32p_row02_traceSegment_086_1296_0013, g32p_row02_traceSegment_086_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1323 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1323 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1323 13 14, g32p_row02_traceSegment_086_1323_0013, g32p_row02_traceSegment_086_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1296 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1296 27 27, g32p_row02_traceSegment_086_1296_0027, g32p_row02_traceSegment_086_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1350 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1350 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1350 13 14, g32p_row02_traceSegment_086_1350_0013, g32p_row02_traceSegment_086_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1377 13 14, g32p_row02_traceSegment_086_1377_0013, g32p_row02_traceSegment_086_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1350 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1350 27 27, g32p_row02_traceSegment_086_1350_0027, g32p_row02_traceSegment_086_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1296 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1296 54 54, g32p_row02_traceSegment_086_1296_0054, g32p_row02_traceSegment_086_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1417 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1404 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1404 13 14, g32p_row02_traceSegment_086_1404_0013, g32p_row02_traceSegment_086_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1431 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1431 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1431 13 14, g32p_row02_traceSegment_086_1431_0013, g32p_row02_traceSegment_086_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1404 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1404 27 27, g32p_row02_traceSegment_086_1404_0027, g32p_row02_traceSegment_086_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1471 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1458 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1458 13 14, g32p_row02_traceSegment_086_1458_0013, g32p_row02_traceSegment_086_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1498 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1485 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1485 13 14, g32p_row02_traceSegment_086_1485_0013, g32p_row02_traceSegment_086_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1458 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1458 27 27, g32p_row02_traceSegment_086_1458_0027, g32p_row02_traceSegment_086_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1404 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1404 54 54, g32p_row02_traceSegment_086_1404_0054, g32p_row02_traceSegment_086_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 1296 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1296 108 108, g32p_row02_traceSegment_086_1296_0108, g32p_row02_traceSegment_086_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1512 13 14, g32p_row02_traceSegment_086_1512_0013, g32p_row02_traceSegment_086_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1539 13 14, g32p_row02_traceSegment_086_1539_0013, g32p_row02_traceSegment_086_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1512 27 27, g32p_row02_traceSegment_086_1512_0027, g32p_row02_traceSegment_086_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1566 13 14, g32p_row02_traceSegment_086_1566_0013, g32p_row02_traceSegment_086_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1593 13 14, g32p_row02_traceSegment_086_1593_0013, g32p_row02_traceSegment_086_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1566 27 27, g32p_row02_traceSegment_086_1566_0027, g32p_row02_traceSegment_086_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1512 54 54, g32p_row02_traceSegment_086_1512_0054, g32p_row02_traceSegment_086_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1620 13 14, g32p_row02_traceSegment_086_1620_0013, g32p_row02_traceSegment_086_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1647 13 14, g32p_row02_traceSegment_086_1647_0013, g32p_row02_traceSegment_086_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1620 27 27, g32p_row02_traceSegment_086_1620_0027, g32p_row02_traceSegment_086_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1674 13 14, g32p_row02_traceSegment_086_1674_0013, g32p_row02_traceSegment_086_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1701 13 14, g32p_row02_traceSegment_086_1701_0013, g32p_row02_traceSegment_086_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1674 27 27, g32p_row02_traceSegment_086_1674_0027, g32p_row02_traceSegment_086_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1620 54 54, g32p_row02_traceSegment_086_1620_0054, g32p_row02_traceSegment_086_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1512 108 108, g32p_row02_traceSegment_086_1512_0108, g32p_row02_traceSegment_086_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 1296 432 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1296 216 216, g32p_row02_traceSegment_086_1296_0216, g32p_row02_traceSegment_086_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_086 864 864 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 864 432 432, g32p_row02_traceSegment_086_0864_0432, g32p_row02_traceSegment_086_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_086 0 1728 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 864 864, g32p_row02_traceSegment_086_0000_0864, g32p_row02_traceSegment_086_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1728 13 14, g32p_row02_traceSegment_086_1728_0013, g32p_row02_traceSegment_086_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1755 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1768 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1755 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1755 13 14, g32p_row02_traceSegment_086_1755_0013, g32p_row02_traceSegment_086_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1728 27 27, g32p_row02_traceSegment_086_1728_0027, g32p_row02_traceSegment_086_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1782 13 14, g32p_row02_traceSegment_086_1782_0013, g32p_row02_traceSegment_086_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1809 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1809 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1809 13 14, g32p_row02_traceSegment_086_1809_0013, g32p_row02_traceSegment_086_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1782 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1782 27 27, g32p_row02_traceSegment_086_1782_0027, g32p_row02_traceSegment_086_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1728 54 54, g32p_row02_traceSegment_086_1728_0054, g32p_row02_traceSegment_086_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1836 13 14, g32p_row02_traceSegment_086_1836_0013, g32p_row02_traceSegment_086_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1863 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1863 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1863 13 14, g32p_row02_traceSegment_086_1863_0013, g32p_row02_traceSegment_086_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1836 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1836 27 27, g32p_row02_traceSegment_086_1836_0027, g32p_row02_traceSegment_086_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1890 13 14, g32p_row02_traceSegment_086_1890_0013, g32p_row02_traceSegment_086_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1917 13 14, g32p_row02_traceSegment_086_1917_0013, g32p_row02_traceSegment_086_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1890 27 27, g32p_row02_traceSegment_086_1890_0027, g32p_row02_traceSegment_086_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1836 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1836 54 54, g32p_row02_traceSegment_086_1836_0054, g32p_row02_traceSegment_086_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1728 108 108, g32p_row02_traceSegment_086_1728_0108, g32p_row02_traceSegment_086_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1944 13 14, g32p_row02_traceSegment_086_1944_0013, g32p_row02_traceSegment_086_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1971 13 14, g32p_row02_traceSegment_086_1971_0013, g32p_row02_traceSegment_086_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1944 27 27, g32p_row02_traceSegment_086_1944_0027, g32p_row02_traceSegment_086_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1998 13 14, g32p_row02_traceSegment_086_1998_0013, g32p_row02_traceSegment_086_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2025 13 14, g32p_row02_traceSegment_086_2025_0013, g32p_row02_traceSegment_086_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1998 27 27, g32p_row02_traceSegment_086_1998_0027, g32p_row02_traceSegment_086_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1944 54 54, g32p_row02_traceSegment_086_1944_0054, g32p_row02_traceSegment_086_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2052 13 14, g32p_row02_traceSegment_086_2052_0013, g32p_row02_traceSegment_086_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2079 13 14, g32p_row02_traceSegment_086_2079_0013, g32p_row02_traceSegment_086_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2052 27 27, g32p_row02_traceSegment_086_2052_0027, g32p_row02_traceSegment_086_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2106 13 14, g32p_row02_traceSegment_086_2106_0013, g32p_row02_traceSegment_086_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2133 13 14, g32p_row02_traceSegment_086_2133_0013, g32p_row02_traceSegment_086_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2106 27 27, g32p_row02_traceSegment_086_2106_0027, g32p_row02_traceSegment_086_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2052 54 54, g32p_row02_traceSegment_086_2052_0054, g32p_row02_traceSegment_086_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1944 108 108, g32p_row02_traceSegment_086_1944_0108, g32p_row02_traceSegment_086_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1728 216 216, g32p_row02_traceSegment_086_1728_0216, g32p_row02_traceSegment_086_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2160 13 14, g32p_row02_traceSegment_086_2160_0013, g32p_row02_traceSegment_086_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2187 13 14, g32p_row02_traceSegment_086_2187_0013, g32p_row02_traceSegment_086_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2160 27 27, g32p_row02_traceSegment_086_2160_0027, g32p_row02_traceSegment_086_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2214 13 14, g32p_row02_traceSegment_086_2214_0013, g32p_row02_traceSegment_086_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2241 13 14, g32p_row02_traceSegment_086_2241_0013, g32p_row02_traceSegment_086_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2214 27 27, g32p_row02_traceSegment_086_2214_0027, g32p_row02_traceSegment_086_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2160 54 54, g32p_row02_traceSegment_086_2160_0054, g32p_row02_traceSegment_086_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2268 13 14, g32p_row02_traceSegment_086_2268_0013, g32p_row02_traceSegment_086_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2295 13 14, g32p_row02_traceSegment_086_2295_0013, g32p_row02_traceSegment_086_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2268 27 27, g32p_row02_traceSegment_086_2268_0027, g32p_row02_traceSegment_086_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2322 13 14, g32p_row02_traceSegment_086_2322_0013, g32p_row02_traceSegment_086_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2349 13 14, g32p_row02_traceSegment_086_2349_0013, g32p_row02_traceSegment_086_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2322 27 27, g32p_row02_traceSegment_086_2322_0027, g32p_row02_traceSegment_086_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2268 54 54, g32p_row02_traceSegment_086_2268_0054, g32p_row02_traceSegment_086_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2160 108 108, g32p_row02_traceSegment_086_2160_0108, g32p_row02_traceSegment_086_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2376 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2376 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2376 13 14, g32p_row02_traceSegment_086_2376_0013, g32p_row02_traceSegment_086_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2403 13 14, g32p_row02_traceSegment_086_2403_0013, g32p_row02_traceSegment_086_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2376 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2376 27 27, g32p_row02_traceSegment_086_2376_0027, g32p_row02_traceSegment_086_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2430 13 14, g32p_row02_traceSegment_086_2430_0013, g32p_row02_traceSegment_086_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2457 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2457 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2457 13 14, g32p_row02_traceSegment_086_2457_0013, g32p_row02_traceSegment_086_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2430 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2430 27 27, g32p_row02_traceSegment_086_2430_0027, g32p_row02_traceSegment_086_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2376 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2376 54 54, g32p_row02_traceSegment_086_2376_0054, g32p_row02_traceSegment_086_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2484 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2497 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2484 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2484 13 14, g32p_row02_traceSegment_086_2484_0013, g32p_row02_traceSegment_086_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2511 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2511 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2511 13 14, g32p_row02_traceSegment_086_2511_0013, g32p_row02_traceSegment_086_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2484 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2484 27 27, g32p_row02_traceSegment_086_2484_0027, g32p_row02_traceSegment_086_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2538 13 14, g32p_row02_traceSegment_086_2538_0013, g32p_row02_traceSegment_086_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2565 13 14, g32p_row02_traceSegment_086_2565_0013, g32p_row02_traceSegment_086_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2538 27 27, g32p_row02_traceSegment_086_2538_0027, g32p_row02_traceSegment_086_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2484 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2484 54 54, g32p_row02_traceSegment_086_2484_0054, g32p_row02_traceSegment_086_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 2376 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2376 108 108, g32p_row02_traceSegment_086_2376_0108, g32p_row02_traceSegment_086_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 2160 432 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2160 216 216, g32p_row02_traceSegment_086_2160_0216, g32p_row02_traceSegment_086_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 864 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1728 432 432, g32p_row02_traceSegment_086_1728_0432, g32p_row02_traceSegment_086_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2592 13 14, g32p_row02_traceSegment_086_2592_0013, g32p_row02_traceSegment_086_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2619 13 14, g32p_row02_traceSegment_086_2619_0013, g32p_row02_traceSegment_086_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2592 27 27, g32p_row02_traceSegment_086_2592_0027, g32p_row02_traceSegment_086_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2646 13 14, g32p_row02_traceSegment_086_2646_0013, g32p_row02_traceSegment_086_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2673 13 14, g32p_row02_traceSegment_086_2673_0013, g32p_row02_traceSegment_086_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2646 27 27, g32p_row02_traceSegment_086_2646_0027, g32p_row02_traceSegment_086_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2592 54 54, g32p_row02_traceSegment_086_2592_0054, g32p_row02_traceSegment_086_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2700 13 14, g32p_row02_traceSegment_086_2700_0013, g32p_row02_traceSegment_086_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2727 13 14, g32p_row02_traceSegment_086_2727_0013, g32p_row02_traceSegment_086_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2700 27 27, g32p_row02_traceSegment_086_2700_0027, g32p_row02_traceSegment_086_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2754 13 14, g32p_row02_traceSegment_086_2754_0013, g32p_row02_traceSegment_086_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2781 13 14, g32p_row02_traceSegment_086_2781_0013, g32p_row02_traceSegment_086_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2754 27 27, g32p_row02_traceSegment_086_2754_0027, g32p_row02_traceSegment_086_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2700 54 54, g32p_row02_traceSegment_086_2700_0054, g32p_row02_traceSegment_086_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2592 108 108, g32p_row02_traceSegment_086_2592_0108, g32p_row02_traceSegment_086_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2808 13 14, g32p_row02_traceSegment_086_2808_0013, g32p_row02_traceSegment_086_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2835 13 14, g32p_row02_traceSegment_086_2835_0013, g32p_row02_traceSegment_086_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2808 27 27, g32p_row02_traceSegment_086_2808_0027, g32p_row02_traceSegment_086_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2862 13 14, g32p_row02_traceSegment_086_2862_0013, g32p_row02_traceSegment_086_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2889 13 14, g32p_row02_traceSegment_086_2889_0013, g32p_row02_traceSegment_086_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2862 27 27, g32p_row02_traceSegment_086_2862_0027, g32p_row02_traceSegment_086_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2808 54 54, g32p_row02_traceSegment_086_2808_0054, g32p_row02_traceSegment_086_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2916 13 14, g32p_row02_traceSegment_086_2916_0013, g32p_row02_traceSegment_086_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2943 13 14, g32p_row02_traceSegment_086_2943_0013, g32p_row02_traceSegment_086_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2916 27 27, g32p_row02_traceSegment_086_2916_0027, g32p_row02_traceSegment_086_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2970 13 14, g32p_row02_traceSegment_086_2970_0013, g32p_row02_traceSegment_086_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2997 13 14, g32p_row02_traceSegment_086_2997_0013, g32p_row02_traceSegment_086_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2970 27 27, g32p_row02_traceSegment_086_2970_0027, g32p_row02_traceSegment_086_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2916 54 54, g32p_row02_traceSegment_086_2916_0054, g32p_row02_traceSegment_086_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2808 108 108, g32p_row02_traceSegment_086_2808_0108, g32p_row02_traceSegment_086_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2592 216 216, g32p_row02_traceSegment_086_2592_0216, g32p_row02_traceSegment_086_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3024 13 14, g32p_row02_traceSegment_086_3024_0013, g32p_row02_traceSegment_086_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3051 13 14, g32p_row02_traceSegment_086_3051_0013, g32p_row02_traceSegment_086_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3024 27 27, g32p_row02_traceSegment_086_3024_0027, g32p_row02_traceSegment_086_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3078 13 14, g32p_row02_traceSegment_086_3078_0013, g32p_row02_traceSegment_086_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3105 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3105 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3105 13 14, g32p_row02_traceSegment_086_3105_0013, g32p_row02_traceSegment_086_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3078 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3078 27 27, g32p_row02_traceSegment_086_3078_0027, g32p_row02_traceSegment_086_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 3024 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3024 54 54, g32p_row02_traceSegment_086_3024_0054, g32p_row02_traceSegment_086_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3145 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3132 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3132 13 14, g32p_row02_traceSegment_086_3132_0013, g32p_row02_traceSegment_086_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3159 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3159 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3159 13 14, g32p_row02_traceSegment_086_3159_0013, g32p_row02_traceSegment_086_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3132 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3132 27 27, g32p_row02_traceSegment_086_3132_0027, g32p_row02_traceSegment_086_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3186 13 14, g32p_row02_traceSegment_086_3186_0013, g32p_row02_traceSegment_086_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3213 13 14, g32p_row02_traceSegment_086_3213_0013, g32p_row02_traceSegment_086_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3186 27 27, g32p_row02_traceSegment_086_3186_0027, g32p_row02_traceSegment_086_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 3132 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3132 54 54, g32p_row02_traceSegment_086_3132_0054, g32p_row02_traceSegment_086_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 3024 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3024 108 108, g32p_row02_traceSegment_086_3024_0108, g32p_row02_traceSegment_086_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3240 13 14, g32p_row02_traceSegment_086_3240_0013, g32p_row02_traceSegment_086_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3280 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3267 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3267 13 14, g32p_row02_traceSegment_086_3267_0013, g32p_row02_traceSegment_086_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3240 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3240 27 27, g32p_row02_traceSegment_086_3240_0027, g32p_row02_traceSegment_086_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3294 13 14, g32p_row02_traceSegment_086_3294_0013, g32p_row02_traceSegment_086_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3321 13 14, g32p_row02_traceSegment_086_3321_0013, g32p_row02_traceSegment_086_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3294 27 27, g32p_row02_traceSegment_086_3294_0027, g32p_row02_traceSegment_086_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 3240 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3240 54 54, g32p_row02_traceSegment_086_3240_0054, g32p_row02_traceSegment_086_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3348 13 14, g32p_row02_traceSegment_086_3348_0013, g32p_row02_traceSegment_086_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3375 13 14, g32p_row02_traceSegment_086_3375_0013, g32p_row02_traceSegment_086_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3348 27 27, g32p_row02_traceSegment_086_3348_0027, g32p_row02_traceSegment_086_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3402 13 14, g32p_row02_traceSegment_086_3402_0013, g32p_row02_traceSegment_086_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_086 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_086 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_086_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_086 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3429 13 14, g32p_row02_traceSegment_086_3429_0013, g32p_row02_traceSegment_086_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_086 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3402 27 27, g32p_row02_traceSegment_086_3402_0027, g32p_row02_traceSegment_086_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_086 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3348 54 54, g32p_row02_traceSegment_086_3348_0054, g32p_row02_traceSegment_086_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_086 3240 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3240 108 108, g32p_row02_traceSegment_086_3240_0108, g32p_row02_traceSegment_086_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_086_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_086 3024 432 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 3024 216 216, g32p_row02_traceSegment_086_3024_0216, g32p_row02_traceSegment_086_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_086_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_086 2592 864 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 2592 432 432, g32p_row02_traceSegment_086_2592_0432, g32p_row02_traceSegment_086_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_086_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_086 1728 1728 = [0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 1728 864 864, g32p_row02_traceSegment_086_1728_0864, g32p_row02_traceSegment_086_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_086_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_086 0 3456 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_086 0 1728 1728, g32p_row02_traceSegment_086_0000_1728, g32p_row02_traceSegment_086_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_086 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 86 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_086_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_087 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 87 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_087_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 13 14, g32p_row02_traceSegment_087_0000_0013, g32p_row02_traceSegment_087_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 27 13 14, g32p_row02_traceSegment_087_0027_0013, g32p_row02_traceSegment_087_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 27 27, g32p_row02_traceSegment_087_0000_0027, g32p_row02_traceSegment_087_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 54 13 14, g32p_row02_traceSegment_087_0054_0013, g32p_row02_traceSegment_087_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 81 13 14, g32p_row02_traceSegment_087_0081_0013, g32p_row02_traceSegment_087_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 54 27 27, g32p_row02_traceSegment_087_0054_0027, g32p_row02_traceSegment_087_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 54 54, g32p_row02_traceSegment_087_0000_0054, g32p_row02_traceSegment_087_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 108 13 14, g32p_row02_traceSegment_087_0108_0013, g32p_row02_traceSegment_087_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 135 13 14, g32p_row02_traceSegment_087_0135_0013, g32p_row02_traceSegment_087_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 108 27 27, g32p_row02_traceSegment_087_0108_0027, g32p_row02_traceSegment_087_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 162 13 14, g32p_row02_traceSegment_087_0162_0013, g32p_row02_traceSegment_087_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 189 13 14, g32p_row02_traceSegment_087_0189_0013, g32p_row02_traceSegment_087_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 162 27 27, g32p_row02_traceSegment_087_0162_0027, g32p_row02_traceSegment_087_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 108 54 54, g32p_row02_traceSegment_087_0108_0054, g32p_row02_traceSegment_087_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 108 108, g32p_row02_traceSegment_087_0000_0108, g32p_row02_traceSegment_087_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 216 13 14, g32p_row02_traceSegment_087_0216_0013, g32p_row02_traceSegment_087_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 243 13 14, g32p_row02_traceSegment_087_0243_0013, g32p_row02_traceSegment_087_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 216 27 27, g32p_row02_traceSegment_087_0216_0027, g32p_row02_traceSegment_087_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 283 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 270 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 270 13 14, g32p_row02_traceSegment_087_0270_0013, g32p_row02_traceSegment_087_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 297 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 297 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 297 13 14, g32p_row02_traceSegment_087_0297_0013, g32p_row02_traceSegment_087_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 270 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 270 27 27, g32p_row02_traceSegment_087_0270_0027, g32p_row02_traceSegment_087_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 216 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 216 54 54, g32p_row02_traceSegment_087_0216_0054, g32p_row02_traceSegment_087_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 324 13 14, g32p_row02_traceSegment_087_0324_0013, g32p_row02_traceSegment_087_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 351 13 14, g32p_row02_traceSegment_087_0351_0013, g32p_row02_traceSegment_087_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 324 27 27, g32p_row02_traceSegment_087_0324_0027, g32p_row02_traceSegment_087_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 378 13 14, g32p_row02_traceSegment_087_0378_0013, g32p_row02_traceSegment_087_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 405 13 14, g32p_row02_traceSegment_087_0405_0013, g32p_row02_traceSegment_087_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 378 27 27, g32p_row02_traceSegment_087_0378_0027, g32p_row02_traceSegment_087_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 324 54 54, g32p_row02_traceSegment_087_0324_0054, g32p_row02_traceSegment_087_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 216 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 216 108 108, g32p_row02_traceSegment_087_0216_0108, g32p_row02_traceSegment_087_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 0 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 216 216, g32p_row02_traceSegment_087_0000_0216, g32p_row02_traceSegment_087_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 432 13 14, g32p_row02_traceSegment_087_0432_0013, g32p_row02_traceSegment_087_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 459 13 14, g32p_row02_traceSegment_087_0459_0013, g32p_row02_traceSegment_087_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 432 27 27, g32p_row02_traceSegment_087_0432_0027, g32p_row02_traceSegment_087_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 486 13 14, g32p_row02_traceSegment_087_0486_0013, g32p_row02_traceSegment_087_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 513 13 14, g32p_row02_traceSegment_087_0513_0013, g32p_row02_traceSegment_087_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 486 27 27, g32p_row02_traceSegment_087_0486_0027, g32p_row02_traceSegment_087_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 432 54 54, g32p_row02_traceSegment_087_0432_0054, g32p_row02_traceSegment_087_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 540 13 14, g32p_row02_traceSegment_087_0540_0013, g32p_row02_traceSegment_087_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 567 13 14, g32p_row02_traceSegment_087_0567_0013, g32p_row02_traceSegment_087_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 540 27 27, g32p_row02_traceSegment_087_0540_0027, g32p_row02_traceSegment_087_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 594 13 14, g32p_row02_traceSegment_087_0594_0013, g32p_row02_traceSegment_087_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 621 13 14, g32p_row02_traceSegment_087_0621_0013, g32p_row02_traceSegment_087_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 594 27 27, g32p_row02_traceSegment_087_0594_0027, g32p_row02_traceSegment_087_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 540 54 54, g32p_row02_traceSegment_087_0540_0054, g32p_row02_traceSegment_087_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 432 108 108, g32p_row02_traceSegment_087_0432_0108, g32p_row02_traceSegment_087_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 648 13 14, g32p_row02_traceSegment_087_0648_0013, g32p_row02_traceSegment_087_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 675 13 14, g32p_row02_traceSegment_087_0675_0013, g32p_row02_traceSegment_087_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 648 27 27, g32p_row02_traceSegment_087_0648_0027, g32p_row02_traceSegment_087_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 702 13 14, g32p_row02_traceSegment_087_0702_0013, g32p_row02_traceSegment_087_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 729 13 14, g32p_row02_traceSegment_087_0729_0013, g32p_row02_traceSegment_087_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 702 27 27, g32p_row02_traceSegment_087_0702_0027, g32p_row02_traceSegment_087_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 648 54 54, g32p_row02_traceSegment_087_0648_0054, g32p_row02_traceSegment_087_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 756 13 14, g32p_row02_traceSegment_087_0756_0013, g32p_row02_traceSegment_087_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 783 13 14, g32p_row02_traceSegment_087_0783_0013, g32p_row02_traceSegment_087_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 756 27 27, g32p_row02_traceSegment_087_0756_0027, g32p_row02_traceSegment_087_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 810 13 14, g32p_row02_traceSegment_087_0810_0013, g32p_row02_traceSegment_087_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 837 13 14, g32p_row02_traceSegment_087_0837_0013, g32p_row02_traceSegment_087_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 810 27 27, g32p_row02_traceSegment_087_0810_0027, g32p_row02_traceSegment_087_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 756 54 54, g32p_row02_traceSegment_087_0756_0054, g32p_row02_traceSegment_087_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 648 108 108, g32p_row02_traceSegment_087_0648_0108, g32p_row02_traceSegment_087_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 432 216 216, g32p_row02_traceSegment_087_0432_0216, g32p_row02_traceSegment_087_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_087 0 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 432 432, g32p_row02_traceSegment_087_0000_0432, g32p_row02_traceSegment_087_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 864 13 14, g32p_row02_traceSegment_087_0864_0013, g32p_row02_traceSegment_087_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 891 13 14, g32p_row02_traceSegment_087_0891_0013, g32p_row02_traceSegment_087_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 864 27 27, g32p_row02_traceSegment_087_0864_0027, g32p_row02_traceSegment_087_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 918 13 14, g32p_row02_traceSegment_087_0918_0013, g32p_row02_traceSegment_087_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 945 13 14, g32p_row02_traceSegment_087_0945_0013, g32p_row02_traceSegment_087_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 918 27 27, g32p_row02_traceSegment_087_0918_0027, g32p_row02_traceSegment_087_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 864 54 54, g32p_row02_traceSegment_087_0864_0054, g32p_row02_traceSegment_087_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 972 13 14, g32p_row02_traceSegment_087_0972_0013, g32p_row02_traceSegment_087_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 999 13 14, g32p_row02_traceSegment_087_0999_0013, g32p_row02_traceSegment_087_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 972 27 27, g32p_row02_traceSegment_087_0972_0027, g32p_row02_traceSegment_087_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1026 13 14, g32p_row02_traceSegment_087_1026_0013, g32p_row02_traceSegment_087_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1053 13 14, g32p_row02_traceSegment_087_1053_0013, g32p_row02_traceSegment_087_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1026 27 27, g32p_row02_traceSegment_087_1026_0027, g32p_row02_traceSegment_087_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 972 54 54, g32p_row02_traceSegment_087_0972_0054, g32p_row02_traceSegment_087_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 864 108 108, g32p_row02_traceSegment_087_0864_0108, g32p_row02_traceSegment_087_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1080 13 14, g32p_row02_traceSegment_087_1080_0013, g32p_row02_traceSegment_087_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1107 13 14, g32p_row02_traceSegment_087_1107_0013, g32p_row02_traceSegment_087_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1080 27 27, g32p_row02_traceSegment_087_1080_0027, g32p_row02_traceSegment_087_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1134 13 14, g32p_row02_traceSegment_087_1134_0013, g32p_row02_traceSegment_087_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1161 13 14, g32p_row02_traceSegment_087_1161_0013, g32p_row02_traceSegment_087_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1134 27 27, g32p_row02_traceSegment_087_1134_0027, g32p_row02_traceSegment_087_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1080 54 54, g32p_row02_traceSegment_087_1080_0054, g32p_row02_traceSegment_087_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1188 13 14, g32p_row02_traceSegment_087_1188_0013, g32p_row02_traceSegment_087_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1215 13 14, g32p_row02_traceSegment_087_1215_0013, g32p_row02_traceSegment_087_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1188 27 27, g32p_row02_traceSegment_087_1188_0027, g32p_row02_traceSegment_087_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1242 13 14, g32p_row02_traceSegment_087_1242_0013, g32p_row02_traceSegment_087_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1269 13 14, g32p_row02_traceSegment_087_1269_0013, g32p_row02_traceSegment_087_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1242 27 27, g32p_row02_traceSegment_087_1242_0027, g32p_row02_traceSegment_087_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1188 54 54, g32p_row02_traceSegment_087_1188_0054, g32p_row02_traceSegment_087_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1080 108 108, g32p_row02_traceSegment_087_1080_0108, g32p_row02_traceSegment_087_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 864 216 216, g32p_row02_traceSegment_087_0864_0216, g32p_row02_traceSegment_087_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1296 13 14, g32p_row02_traceSegment_087_1296_0013, g32p_row02_traceSegment_087_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1323 13 14, g32p_row02_traceSegment_087_1323_0013, g32p_row02_traceSegment_087_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1296 27 27, g32p_row02_traceSegment_087_1296_0027, g32p_row02_traceSegment_087_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1350 13 14, g32p_row02_traceSegment_087_1350_0013, g32p_row02_traceSegment_087_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1377 13 14, g32p_row02_traceSegment_087_1377_0013, g32p_row02_traceSegment_087_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1350 27 27, g32p_row02_traceSegment_087_1350_0027, g32p_row02_traceSegment_087_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1296 54 54, g32p_row02_traceSegment_087_1296_0054, g32p_row02_traceSegment_087_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1404 13 14, g32p_row02_traceSegment_087_1404_0013, g32p_row02_traceSegment_087_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1431 13 14, g32p_row02_traceSegment_087_1431_0013, g32p_row02_traceSegment_087_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1404 27 27, g32p_row02_traceSegment_087_1404_0027, g32p_row02_traceSegment_087_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1458 13 14, g32p_row02_traceSegment_087_1458_0013, g32p_row02_traceSegment_087_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1485 13 14, g32p_row02_traceSegment_087_1485_0013, g32p_row02_traceSegment_087_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1458 27 27, g32p_row02_traceSegment_087_1458_0027, g32p_row02_traceSegment_087_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1404 54 54, g32p_row02_traceSegment_087_1404_0054, g32p_row02_traceSegment_087_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1296 108 108, g32p_row02_traceSegment_087_1296_0108, g32p_row02_traceSegment_087_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1512 13 14, g32p_row02_traceSegment_087_1512_0013, g32p_row02_traceSegment_087_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1539 13 14, g32p_row02_traceSegment_087_1539_0013, g32p_row02_traceSegment_087_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1512 27 27, g32p_row02_traceSegment_087_1512_0027, g32p_row02_traceSegment_087_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1566 13 14, g32p_row02_traceSegment_087_1566_0013, g32p_row02_traceSegment_087_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1593 13 14, g32p_row02_traceSegment_087_1593_0013, g32p_row02_traceSegment_087_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1566 27 27, g32p_row02_traceSegment_087_1566_0027, g32p_row02_traceSegment_087_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1512 54 54, g32p_row02_traceSegment_087_1512_0054, g32p_row02_traceSegment_087_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1620 13 14, g32p_row02_traceSegment_087_1620_0013, g32p_row02_traceSegment_087_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1647 13 14, g32p_row02_traceSegment_087_1647_0013, g32p_row02_traceSegment_087_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1620 27 27, g32p_row02_traceSegment_087_1620_0027, g32p_row02_traceSegment_087_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1674 13 14, g32p_row02_traceSegment_087_1674_0013, g32p_row02_traceSegment_087_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1701 13 14, g32p_row02_traceSegment_087_1701_0013, g32p_row02_traceSegment_087_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1674 27 27, g32p_row02_traceSegment_087_1674_0027, g32p_row02_traceSegment_087_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1620 54 54, g32p_row02_traceSegment_087_1620_0054, g32p_row02_traceSegment_087_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1512 108 108, g32p_row02_traceSegment_087_1512_0108, g32p_row02_traceSegment_087_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1296 216 216, g32p_row02_traceSegment_087_1296_0216, g32p_row02_traceSegment_087_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_087 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 864 432 432, g32p_row02_traceSegment_087_0864_0432, g32p_row02_traceSegment_087_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_087 0 1728 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 864 864, g32p_row02_traceSegment_087_0000_0864, g32p_row02_traceSegment_087_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1728 13 14, g32p_row02_traceSegment_087_1728_0013, g32p_row02_traceSegment_087_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1755 13 14, g32p_row02_traceSegment_087_1755_0013, g32p_row02_traceSegment_087_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1728 27 27, g32p_row02_traceSegment_087_1728_0027, g32p_row02_traceSegment_087_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1782 13 14, g32p_row02_traceSegment_087_1782_0013, g32p_row02_traceSegment_087_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1809 13 14, g32p_row02_traceSegment_087_1809_0013, g32p_row02_traceSegment_087_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1782 27 27, g32p_row02_traceSegment_087_1782_0027, g32p_row02_traceSegment_087_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1728 54 54, g32p_row02_traceSegment_087_1728_0054, g32p_row02_traceSegment_087_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1836 13 14, g32p_row02_traceSegment_087_1836_0013, g32p_row02_traceSegment_087_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1863 13 14, g32p_row02_traceSegment_087_1863_0013, g32p_row02_traceSegment_087_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1836 27 27, g32p_row02_traceSegment_087_1836_0027, g32p_row02_traceSegment_087_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1890 13 14, g32p_row02_traceSegment_087_1890_0013, g32p_row02_traceSegment_087_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1917 13 14, g32p_row02_traceSegment_087_1917_0013, g32p_row02_traceSegment_087_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1890 27 27, g32p_row02_traceSegment_087_1890_0027, g32p_row02_traceSegment_087_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1836 54 54, g32p_row02_traceSegment_087_1836_0054, g32p_row02_traceSegment_087_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1728 108 108, g32p_row02_traceSegment_087_1728_0108, g32p_row02_traceSegment_087_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1944 13 14, g32p_row02_traceSegment_087_1944_0013, g32p_row02_traceSegment_087_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1971 13 14, g32p_row02_traceSegment_087_1971_0013, g32p_row02_traceSegment_087_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1944 27 27, g32p_row02_traceSegment_087_1944_0027, g32p_row02_traceSegment_087_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1998 13 14, g32p_row02_traceSegment_087_1998_0013, g32p_row02_traceSegment_087_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2025 13 14, g32p_row02_traceSegment_087_2025_0013, g32p_row02_traceSegment_087_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1998 27 27, g32p_row02_traceSegment_087_1998_0027, g32p_row02_traceSegment_087_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1944 54 54, g32p_row02_traceSegment_087_1944_0054, g32p_row02_traceSegment_087_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2052 13 14, g32p_row02_traceSegment_087_2052_0013, g32p_row02_traceSegment_087_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2079 13 14, g32p_row02_traceSegment_087_2079_0013, g32p_row02_traceSegment_087_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2052 27 27, g32p_row02_traceSegment_087_2052_0027, g32p_row02_traceSegment_087_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2106 13 14, g32p_row02_traceSegment_087_2106_0013, g32p_row02_traceSegment_087_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2133 13 14, g32p_row02_traceSegment_087_2133_0013, g32p_row02_traceSegment_087_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2106 27 27, g32p_row02_traceSegment_087_2106_0027, g32p_row02_traceSegment_087_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2052 54 54, g32p_row02_traceSegment_087_2052_0054, g32p_row02_traceSegment_087_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1944 108 108, g32p_row02_traceSegment_087_1944_0108, g32p_row02_traceSegment_087_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1728 216 216, g32p_row02_traceSegment_087_1728_0216, g32p_row02_traceSegment_087_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2160 13 14, g32p_row02_traceSegment_087_2160_0013, g32p_row02_traceSegment_087_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2187 13 14, g32p_row02_traceSegment_087_2187_0013, g32p_row02_traceSegment_087_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2160 27 27, g32p_row02_traceSegment_087_2160_0027, g32p_row02_traceSegment_087_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2214 13 14, g32p_row02_traceSegment_087_2214_0013, g32p_row02_traceSegment_087_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2241 13 14, g32p_row02_traceSegment_087_2241_0013, g32p_row02_traceSegment_087_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2214 27 27, g32p_row02_traceSegment_087_2214_0027, g32p_row02_traceSegment_087_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2160 54 54, g32p_row02_traceSegment_087_2160_0054, g32p_row02_traceSegment_087_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2268 13 14, g32p_row02_traceSegment_087_2268_0013, g32p_row02_traceSegment_087_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2295 13 14, g32p_row02_traceSegment_087_2295_0013, g32p_row02_traceSegment_087_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2268 27 27, g32p_row02_traceSegment_087_2268_0027, g32p_row02_traceSegment_087_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2322 13 14, g32p_row02_traceSegment_087_2322_0013, g32p_row02_traceSegment_087_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2349 13 14, g32p_row02_traceSegment_087_2349_0013, g32p_row02_traceSegment_087_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2322 27 27, g32p_row02_traceSegment_087_2322_0027, g32p_row02_traceSegment_087_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2268 54 54, g32p_row02_traceSegment_087_2268_0054, g32p_row02_traceSegment_087_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2160 108 108, g32p_row02_traceSegment_087_2160_0108, g32p_row02_traceSegment_087_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2376 13 14, g32p_row02_traceSegment_087_2376_0013, g32p_row02_traceSegment_087_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2403 13 14, g32p_row02_traceSegment_087_2403_0013, g32p_row02_traceSegment_087_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2376 27 27, g32p_row02_traceSegment_087_2376_0027, g32p_row02_traceSegment_087_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2443 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2430 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2430 13 14, g32p_row02_traceSegment_087_2430_0013, g32p_row02_traceSegment_087_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2457 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2457 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2457 13 14, g32p_row02_traceSegment_087_2457_0013, g32p_row02_traceSegment_087_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2430 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2430 27 27, g32p_row02_traceSegment_087_2430_0027, g32p_row02_traceSegment_087_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2376 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2376 54 54, g32p_row02_traceSegment_087_2376_0054, g32p_row02_traceSegment_087_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2484 13 14, g32p_row02_traceSegment_087_2484_0013, g32p_row02_traceSegment_087_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2511 13 14, g32p_row02_traceSegment_087_2511_0013, g32p_row02_traceSegment_087_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2484 27 27, g32p_row02_traceSegment_087_2484_0027, g32p_row02_traceSegment_087_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2538 13 14, g32p_row02_traceSegment_087_2538_0013, g32p_row02_traceSegment_087_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2565 13 14, g32p_row02_traceSegment_087_2565_0013, g32p_row02_traceSegment_087_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2538 27 27, g32p_row02_traceSegment_087_2538_0027, g32p_row02_traceSegment_087_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2484 54 54, g32p_row02_traceSegment_087_2484_0054, g32p_row02_traceSegment_087_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 2376 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2376 108 108, g32p_row02_traceSegment_087_2376_0108, g32p_row02_traceSegment_087_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 2160 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2160 216 216, g32p_row02_traceSegment_087_2160_0216, g32p_row02_traceSegment_087_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1728 432 432, g32p_row02_traceSegment_087_1728_0432, g32p_row02_traceSegment_087_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2592 13 14, g32p_row02_traceSegment_087_2592_0013, g32p_row02_traceSegment_087_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2619 13 14, g32p_row02_traceSegment_087_2619_0013, g32p_row02_traceSegment_087_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2592 27 27, g32p_row02_traceSegment_087_2592_0027, g32p_row02_traceSegment_087_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2646 13 14, g32p_row02_traceSegment_087_2646_0013, g32p_row02_traceSegment_087_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2673 13 14, g32p_row02_traceSegment_087_2673_0013, g32p_row02_traceSegment_087_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2646 27 27, g32p_row02_traceSegment_087_2646_0027, g32p_row02_traceSegment_087_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2592 54 54, g32p_row02_traceSegment_087_2592_0054, g32p_row02_traceSegment_087_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2700 13 14, g32p_row02_traceSegment_087_2700_0013, g32p_row02_traceSegment_087_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2727 13 14, g32p_row02_traceSegment_087_2727_0013, g32p_row02_traceSegment_087_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2700 27 27, g32p_row02_traceSegment_087_2700_0027, g32p_row02_traceSegment_087_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2754 13 14, g32p_row02_traceSegment_087_2754_0013, g32p_row02_traceSegment_087_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2781 13 14, g32p_row02_traceSegment_087_2781_0013, g32p_row02_traceSegment_087_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2754 27 27, g32p_row02_traceSegment_087_2754_0027, g32p_row02_traceSegment_087_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2700 54 54, g32p_row02_traceSegment_087_2700_0054, g32p_row02_traceSegment_087_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2592 108 108, g32p_row02_traceSegment_087_2592_0108, g32p_row02_traceSegment_087_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2808 13 14, g32p_row02_traceSegment_087_2808_0013, g32p_row02_traceSegment_087_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2835 13 14, g32p_row02_traceSegment_087_2835_0013, g32p_row02_traceSegment_087_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2808 27 27, g32p_row02_traceSegment_087_2808_0027, g32p_row02_traceSegment_087_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2862 13 14, g32p_row02_traceSegment_087_2862_0013, g32p_row02_traceSegment_087_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2889 13 14, g32p_row02_traceSegment_087_2889_0013, g32p_row02_traceSegment_087_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2862 27 27, g32p_row02_traceSegment_087_2862_0027, g32p_row02_traceSegment_087_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2808 54 54, g32p_row02_traceSegment_087_2808_0054, g32p_row02_traceSegment_087_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2916 13 14, g32p_row02_traceSegment_087_2916_0013, g32p_row02_traceSegment_087_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2943 13 14, g32p_row02_traceSegment_087_2943_0013, g32p_row02_traceSegment_087_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2916 27 27, g32p_row02_traceSegment_087_2916_0027, g32p_row02_traceSegment_087_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2970 13 14, g32p_row02_traceSegment_087_2970_0013, g32p_row02_traceSegment_087_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2997 13 14, g32p_row02_traceSegment_087_2997_0013, g32p_row02_traceSegment_087_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2970 27 27, g32p_row02_traceSegment_087_2970_0027, g32p_row02_traceSegment_087_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2916 54 54, g32p_row02_traceSegment_087_2916_0054, g32p_row02_traceSegment_087_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2808 108 108, g32p_row02_traceSegment_087_2808_0108, g32p_row02_traceSegment_087_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2592 216 216, g32p_row02_traceSegment_087_2592_0216, g32p_row02_traceSegment_087_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3024 13 14, g32p_row02_traceSegment_087_3024_0013, g32p_row02_traceSegment_087_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3051 13 14, g32p_row02_traceSegment_087_3051_0013, g32p_row02_traceSegment_087_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3024 27 27, g32p_row02_traceSegment_087_3024_0027, g32p_row02_traceSegment_087_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3078 13 14, g32p_row02_traceSegment_087_3078_0013, g32p_row02_traceSegment_087_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3118 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3105 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3105 13 14, g32p_row02_traceSegment_087_3105_0013, g32p_row02_traceSegment_087_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3078 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3078 27 27, g32p_row02_traceSegment_087_3078_0027, g32p_row02_traceSegment_087_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 3024 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3024 54 54, g32p_row02_traceSegment_087_3024_0054, g32p_row02_traceSegment_087_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3132 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3145 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3132 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3132 13 14, g32p_row02_traceSegment_087_3132_0013, g32p_row02_traceSegment_087_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3159 13 14, g32p_row02_traceSegment_087_3159_0013, g32p_row02_traceSegment_087_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3132 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3132 27 27, g32p_row02_traceSegment_087_3132_0027, g32p_row02_traceSegment_087_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3186 13 14, g32p_row02_traceSegment_087_3186_0013, g32p_row02_traceSegment_087_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3213 13 14, g32p_row02_traceSegment_087_3213_0013, g32p_row02_traceSegment_087_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3186 27 27, g32p_row02_traceSegment_087_3186_0027, g32p_row02_traceSegment_087_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 3132 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3132 54 54, g32p_row02_traceSegment_087_3132_0054, g32p_row02_traceSegment_087_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 3024 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3024 108 108, g32p_row02_traceSegment_087_3024_0108, g32p_row02_traceSegment_087_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3240 13 14, g32p_row02_traceSegment_087_3240_0013, g32p_row02_traceSegment_087_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3267 13 14, g32p_row02_traceSegment_087_3267_0013, g32p_row02_traceSegment_087_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3240 27 27, g32p_row02_traceSegment_087_3240_0027, g32p_row02_traceSegment_087_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3294 13 14, g32p_row02_traceSegment_087_3294_0013, g32p_row02_traceSegment_087_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3321 13 14, g32p_row02_traceSegment_087_3321_0013, g32p_row02_traceSegment_087_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3294 27 27, g32p_row02_traceSegment_087_3294_0027, g32p_row02_traceSegment_087_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3240 54 54, g32p_row02_traceSegment_087_3240_0054, g32p_row02_traceSegment_087_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3348 13 14, g32p_row02_traceSegment_087_3348_0013, g32p_row02_traceSegment_087_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3375 13 14, g32p_row02_traceSegment_087_3375_0013, g32p_row02_traceSegment_087_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3348 27 27, g32p_row02_traceSegment_087_3348_0027, g32p_row02_traceSegment_087_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3402 13 14, g32p_row02_traceSegment_087_3402_0013, g32p_row02_traceSegment_087_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_087 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_087 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_087_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_087 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3429 13 14, g32p_row02_traceSegment_087_3429_0013, g32p_row02_traceSegment_087_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_087 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3402 27 27, g32p_row02_traceSegment_087_3402_0027, g32p_row02_traceSegment_087_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_087 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3348 54 54, g32p_row02_traceSegment_087_3348_0054, g32p_row02_traceSegment_087_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_087 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3240 108 108, g32p_row02_traceSegment_087_3240_0108, g32p_row02_traceSegment_087_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_087_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_087 3024 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 3024 216 216, g32p_row02_traceSegment_087_3024_0216, g32p_row02_traceSegment_087_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_087_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_087 2592 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 2592 432 432, g32p_row02_traceSegment_087_2592_0432, g32p_row02_traceSegment_087_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_087_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_087 1728 1728 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 1728 864 864, g32p_row02_traceSegment_087_1728_0864, g32p_row02_traceSegment_087_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_087_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_087 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_087 0 1728 1728, g32p_row02_traceSegment_087_0000_1728, g32p_row02_traceSegment_087_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_087 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 87 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_087_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_088 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 88 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_088_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 13 14, g32p_row02_traceSegment_088_0000_0013, g32p_row02_traceSegment_088_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 27 13 14, g32p_row02_traceSegment_088_0027_0013, g32p_row02_traceSegment_088_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 27 27, g32p_row02_traceSegment_088_0000_0027, g32p_row02_traceSegment_088_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 54 13 14, g32p_row02_traceSegment_088_0054_0013, g32p_row02_traceSegment_088_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 81 13 14, g32p_row02_traceSegment_088_0081_0013, g32p_row02_traceSegment_088_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 54 27 27, g32p_row02_traceSegment_088_0054_0027, g32p_row02_traceSegment_088_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 54 54, g32p_row02_traceSegment_088_0000_0054, g32p_row02_traceSegment_088_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 108 13 14, g32p_row02_traceSegment_088_0108_0013, g32p_row02_traceSegment_088_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 135 13 14, g32p_row02_traceSegment_088_0135_0013, g32p_row02_traceSegment_088_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 108 27 27, g32p_row02_traceSegment_088_0108_0027, g32p_row02_traceSegment_088_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 162 13 14, g32p_row02_traceSegment_088_0162_0013, g32p_row02_traceSegment_088_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 189 13 14, g32p_row02_traceSegment_088_0189_0013, g32p_row02_traceSegment_088_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 162 27 27, g32p_row02_traceSegment_088_0162_0027, g32p_row02_traceSegment_088_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 108 54 54, g32p_row02_traceSegment_088_0108_0054, g32p_row02_traceSegment_088_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 108 108, g32p_row02_traceSegment_088_0000_0108, g32p_row02_traceSegment_088_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 216 13 14, g32p_row02_traceSegment_088_0216_0013, g32p_row02_traceSegment_088_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 243 13 14, g32p_row02_traceSegment_088_0243_0013, g32p_row02_traceSegment_088_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 216 27 27, g32p_row02_traceSegment_088_0216_0027, g32p_row02_traceSegment_088_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 270 13 14, g32p_row02_traceSegment_088_0270_0013, g32p_row02_traceSegment_088_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 297 13 14, g32p_row02_traceSegment_088_0297_0013, g32p_row02_traceSegment_088_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 270 27 27, g32p_row02_traceSegment_088_0270_0027, g32p_row02_traceSegment_088_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 216 54 54, g32p_row02_traceSegment_088_0216_0054, g32p_row02_traceSegment_088_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 324 13 14, g32p_row02_traceSegment_088_0324_0013, g32p_row02_traceSegment_088_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 351 13 14, g32p_row02_traceSegment_088_0351_0013, g32p_row02_traceSegment_088_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 324 27 27, g32p_row02_traceSegment_088_0324_0027, g32p_row02_traceSegment_088_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 378 13 14, g32p_row02_traceSegment_088_0378_0013, g32p_row02_traceSegment_088_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 405 13 14, g32p_row02_traceSegment_088_0405_0013, g32p_row02_traceSegment_088_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 378 27 27, g32p_row02_traceSegment_088_0378_0027, g32p_row02_traceSegment_088_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 324 54 54, g32p_row02_traceSegment_088_0324_0054, g32p_row02_traceSegment_088_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 216 108 108, g32p_row02_traceSegment_088_0216_0108, g32p_row02_traceSegment_088_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 216 216, g32p_row02_traceSegment_088_0000_0216, g32p_row02_traceSegment_088_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 432 13 14, g32p_row02_traceSegment_088_0432_0013, g32p_row02_traceSegment_088_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 459 13 14, g32p_row02_traceSegment_088_0459_0013, g32p_row02_traceSegment_088_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 432 27 27, g32p_row02_traceSegment_088_0432_0027, g32p_row02_traceSegment_088_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 486 13 14, g32p_row02_traceSegment_088_0486_0013, g32p_row02_traceSegment_088_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 513 13 14, g32p_row02_traceSegment_088_0513_0013, g32p_row02_traceSegment_088_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 486 27 27, g32p_row02_traceSegment_088_0486_0027, g32p_row02_traceSegment_088_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 432 54 54, g32p_row02_traceSegment_088_0432_0054, g32p_row02_traceSegment_088_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 540 13 14, g32p_row02_traceSegment_088_0540_0013, g32p_row02_traceSegment_088_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 567 13 14, g32p_row02_traceSegment_088_0567_0013, g32p_row02_traceSegment_088_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 540 27 27, g32p_row02_traceSegment_088_0540_0027, g32p_row02_traceSegment_088_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 594 13 14, g32p_row02_traceSegment_088_0594_0013, g32p_row02_traceSegment_088_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 621 13 14, g32p_row02_traceSegment_088_0621_0013, g32p_row02_traceSegment_088_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 594 27 27, g32p_row02_traceSegment_088_0594_0027, g32p_row02_traceSegment_088_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 540 54 54, g32p_row02_traceSegment_088_0540_0054, g32p_row02_traceSegment_088_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 432 108 108, g32p_row02_traceSegment_088_0432_0108, g32p_row02_traceSegment_088_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 648 13 14, g32p_row02_traceSegment_088_0648_0013, g32p_row02_traceSegment_088_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 675 13 14, g32p_row02_traceSegment_088_0675_0013, g32p_row02_traceSegment_088_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 648 27 27, g32p_row02_traceSegment_088_0648_0027, g32p_row02_traceSegment_088_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 702 13 14, g32p_row02_traceSegment_088_0702_0013, g32p_row02_traceSegment_088_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 729 13 14, g32p_row02_traceSegment_088_0729_0013, g32p_row02_traceSegment_088_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 702 27 27, g32p_row02_traceSegment_088_0702_0027, g32p_row02_traceSegment_088_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 648 54 54, g32p_row02_traceSegment_088_0648_0054, g32p_row02_traceSegment_088_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 756 13 14, g32p_row02_traceSegment_088_0756_0013, g32p_row02_traceSegment_088_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 783 13 14, g32p_row02_traceSegment_088_0783_0013, g32p_row02_traceSegment_088_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 756 27 27, g32p_row02_traceSegment_088_0756_0027, g32p_row02_traceSegment_088_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 810 13 14, g32p_row02_traceSegment_088_0810_0013, g32p_row02_traceSegment_088_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 837 13 14, g32p_row02_traceSegment_088_0837_0013, g32p_row02_traceSegment_088_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 810 27 27, g32p_row02_traceSegment_088_0810_0027, g32p_row02_traceSegment_088_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 756 54 54, g32p_row02_traceSegment_088_0756_0054, g32p_row02_traceSegment_088_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 648 108 108, g32p_row02_traceSegment_088_0648_0108, g32p_row02_traceSegment_088_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 432 216 216, g32p_row02_traceSegment_088_0432_0216, g32p_row02_traceSegment_088_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_088 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 432 432, g32p_row02_traceSegment_088_0000_0432, g32p_row02_traceSegment_088_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 877 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 864 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 864 13 14, g32p_row02_traceSegment_088_0864_0013, g32p_row02_traceSegment_088_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 891 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 891 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 891 13 14, g32p_row02_traceSegment_088_0891_0013, g32p_row02_traceSegment_088_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 864 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 864 27 27, g32p_row02_traceSegment_088_0864_0027, g32p_row02_traceSegment_088_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 931 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 918 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 918 13 14, g32p_row02_traceSegment_088_0918_0013, g32p_row02_traceSegment_088_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 945 13 14, g32p_row02_traceSegment_088_0945_0013, g32p_row02_traceSegment_088_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 918 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 918 27 27, g32p_row02_traceSegment_088_0918_0027, g32p_row02_traceSegment_088_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 864 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 864 54 54, g32p_row02_traceSegment_088_0864_0054, g32p_row02_traceSegment_088_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 972 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 972 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 972 13 14, g32p_row02_traceSegment_088_0972_0013, g32p_row02_traceSegment_088_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 999 13 14, g32p_row02_traceSegment_088_0999_0013, g32p_row02_traceSegment_088_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 972 27 27, g32p_row02_traceSegment_088_0972_0027, g32p_row02_traceSegment_088_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1026 13 14, g32p_row02_traceSegment_088_1026_0013, g32p_row02_traceSegment_088_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1053 13 14, g32p_row02_traceSegment_088_1053_0013, g32p_row02_traceSegment_088_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1026 27 27, g32p_row02_traceSegment_088_1026_0027, g32p_row02_traceSegment_088_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 972 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 972 54 54, g32p_row02_traceSegment_088_0972_0054, g32p_row02_traceSegment_088_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 864 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 864 108 108, g32p_row02_traceSegment_088_0864_0108, g32p_row02_traceSegment_088_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1080 13 14, g32p_row02_traceSegment_088_1080_0013, g32p_row02_traceSegment_088_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1107 13 14, g32p_row02_traceSegment_088_1107_0013, g32p_row02_traceSegment_088_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1080 27 27, g32p_row02_traceSegment_088_1080_0027, g32p_row02_traceSegment_088_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1134 13 14, g32p_row02_traceSegment_088_1134_0013, g32p_row02_traceSegment_088_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1161 13 14, g32p_row02_traceSegment_088_1161_0013, g32p_row02_traceSegment_088_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1134 27 27, g32p_row02_traceSegment_088_1134_0027, g32p_row02_traceSegment_088_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1080 54 54, g32p_row02_traceSegment_088_1080_0054, g32p_row02_traceSegment_088_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1188 13 14, g32p_row02_traceSegment_088_1188_0013, g32p_row02_traceSegment_088_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1215 13 14, g32p_row02_traceSegment_088_1215_0013, g32p_row02_traceSegment_088_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1188 27 27, g32p_row02_traceSegment_088_1188_0027, g32p_row02_traceSegment_088_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1242 13 14, g32p_row02_traceSegment_088_1242_0013, g32p_row02_traceSegment_088_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1269 13 14, g32p_row02_traceSegment_088_1269_0013, g32p_row02_traceSegment_088_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1242 27 27, g32p_row02_traceSegment_088_1242_0027, g32p_row02_traceSegment_088_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1188 54 54, g32p_row02_traceSegment_088_1188_0054, g32p_row02_traceSegment_088_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1080 108 108, g32p_row02_traceSegment_088_1080_0108, g32p_row02_traceSegment_088_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 864 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 864 216 216, g32p_row02_traceSegment_088_0864_0216, g32p_row02_traceSegment_088_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1296 13 14, g32p_row02_traceSegment_088_1296_0013, g32p_row02_traceSegment_088_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1323 13 14, g32p_row02_traceSegment_088_1323_0013, g32p_row02_traceSegment_088_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1296 27 27, g32p_row02_traceSegment_088_1296_0027, g32p_row02_traceSegment_088_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1350 13 14, g32p_row02_traceSegment_088_1350_0013, g32p_row02_traceSegment_088_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1377 13 14, g32p_row02_traceSegment_088_1377_0013, g32p_row02_traceSegment_088_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1350 27 27, g32p_row02_traceSegment_088_1350_0027, g32p_row02_traceSegment_088_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1296 54 54, g32p_row02_traceSegment_088_1296_0054, g32p_row02_traceSegment_088_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1404 13 14, g32p_row02_traceSegment_088_1404_0013, g32p_row02_traceSegment_088_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1431 13 14, g32p_row02_traceSegment_088_1431_0013, g32p_row02_traceSegment_088_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1404 27 27, g32p_row02_traceSegment_088_1404_0027, g32p_row02_traceSegment_088_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1458 13 14, g32p_row02_traceSegment_088_1458_0013, g32p_row02_traceSegment_088_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1485 13 14, g32p_row02_traceSegment_088_1485_0013, g32p_row02_traceSegment_088_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1458 27 27, g32p_row02_traceSegment_088_1458_0027, g32p_row02_traceSegment_088_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1404 54 54, g32p_row02_traceSegment_088_1404_0054, g32p_row02_traceSegment_088_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1296 108 108, g32p_row02_traceSegment_088_1296_0108, g32p_row02_traceSegment_088_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1512 13 14, g32p_row02_traceSegment_088_1512_0013, g32p_row02_traceSegment_088_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1539 13 14, g32p_row02_traceSegment_088_1539_0013, g32p_row02_traceSegment_088_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1512 27 27, g32p_row02_traceSegment_088_1512_0027, g32p_row02_traceSegment_088_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1566 13 14, g32p_row02_traceSegment_088_1566_0013, g32p_row02_traceSegment_088_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1593 13 14, g32p_row02_traceSegment_088_1593_0013, g32p_row02_traceSegment_088_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1566 27 27, g32p_row02_traceSegment_088_1566_0027, g32p_row02_traceSegment_088_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1512 54 54, g32p_row02_traceSegment_088_1512_0054, g32p_row02_traceSegment_088_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1620 13 14, g32p_row02_traceSegment_088_1620_0013, g32p_row02_traceSegment_088_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1647 13 14, g32p_row02_traceSegment_088_1647_0013, g32p_row02_traceSegment_088_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1620 27 27, g32p_row02_traceSegment_088_1620_0027, g32p_row02_traceSegment_088_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1674 13 14, g32p_row02_traceSegment_088_1674_0013, g32p_row02_traceSegment_088_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1701 13 14, g32p_row02_traceSegment_088_1701_0013, g32p_row02_traceSegment_088_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1674 27 27, g32p_row02_traceSegment_088_1674_0027, g32p_row02_traceSegment_088_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1620 54 54, g32p_row02_traceSegment_088_1620_0054, g32p_row02_traceSegment_088_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1512 108 108, g32p_row02_traceSegment_088_1512_0108, g32p_row02_traceSegment_088_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1296 216 216, g32p_row02_traceSegment_088_1296_0216, g32p_row02_traceSegment_088_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_088 864 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 864 432 432, g32p_row02_traceSegment_088_0864_0432, g32p_row02_traceSegment_088_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_088 0 1728 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 864 864, g32p_row02_traceSegment_088_0000_0864, g32p_row02_traceSegment_088_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1728 13 14, g32p_row02_traceSegment_088_1728_0013, g32p_row02_traceSegment_088_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1755 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1755 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1755 13 14, g32p_row02_traceSegment_088_1755_0013, g32p_row02_traceSegment_088_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1728 27 27, g32p_row02_traceSegment_088_1728_0027, g32p_row02_traceSegment_088_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1782 13 14, g32p_row02_traceSegment_088_1782_0013, g32p_row02_traceSegment_088_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1809 13 14, g32p_row02_traceSegment_088_1809_0013, g32p_row02_traceSegment_088_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1782 27 27, g32p_row02_traceSegment_088_1782_0027, g32p_row02_traceSegment_088_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1728 54 54, g32p_row02_traceSegment_088_1728_0054, g32p_row02_traceSegment_088_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1836 13 14, g32p_row02_traceSegment_088_1836_0013, g32p_row02_traceSegment_088_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1863 13 14, g32p_row02_traceSegment_088_1863_0013, g32p_row02_traceSegment_088_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1836 27 27, g32p_row02_traceSegment_088_1836_0027, g32p_row02_traceSegment_088_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1890 13 14, g32p_row02_traceSegment_088_1890_0013, g32p_row02_traceSegment_088_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1917 13 14, g32p_row02_traceSegment_088_1917_0013, g32p_row02_traceSegment_088_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1890 27 27, g32p_row02_traceSegment_088_1890_0027, g32p_row02_traceSegment_088_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1836 54 54, g32p_row02_traceSegment_088_1836_0054, g32p_row02_traceSegment_088_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1728 108 108, g32p_row02_traceSegment_088_1728_0108, g32p_row02_traceSegment_088_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1944 13 14, g32p_row02_traceSegment_088_1944_0013, g32p_row02_traceSegment_088_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1971 13 14, g32p_row02_traceSegment_088_1971_0013, g32p_row02_traceSegment_088_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1944 27 27, g32p_row02_traceSegment_088_1944_0027, g32p_row02_traceSegment_088_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1998 13 14, g32p_row02_traceSegment_088_1998_0013, g32p_row02_traceSegment_088_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2025 13 14, g32p_row02_traceSegment_088_2025_0013, g32p_row02_traceSegment_088_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1998 27 27, g32p_row02_traceSegment_088_1998_0027, g32p_row02_traceSegment_088_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1944 54 54, g32p_row02_traceSegment_088_1944_0054, g32p_row02_traceSegment_088_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2052 13 14, g32p_row02_traceSegment_088_2052_0013, g32p_row02_traceSegment_088_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2079 13 14, g32p_row02_traceSegment_088_2079_0013, g32p_row02_traceSegment_088_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2052 27 27, g32p_row02_traceSegment_088_2052_0027, g32p_row02_traceSegment_088_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2119 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2106 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2106 13 14, g32p_row02_traceSegment_088_2106_0013, g32p_row02_traceSegment_088_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2133 13 14, g32p_row02_traceSegment_088_2133_0013, g32p_row02_traceSegment_088_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2106 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2106 27 27, g32p_row02_traceSegment_088_2106_0027, g32p_row02_traceSegment_088_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2052 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2052 54 54, g32p_row02_traceSegment_088_2052_0054, g32p_row02_traceSegment_088_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 1944 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1944 108 108, g32p_row02_traceSegment_088_1944_0108, g32p_row02_traceSegment_088_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1728 216 216, g32p_row02_traceSegment_088_1728_0216, g32p_row02_traceSegment_088_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2160 13 14, g32p_row02_traceSegment_088_2160_0013, g32p_row02_traceSegment_088_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2187 13 14, g32p_row02_traceSegment_088_2187_0013, g32p_row02_traceSegment_088_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2160 27 27, g32p_row02_traceSegment_088_2160_0027, g32p_row02_traceSegment_088_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2214 13 14, g32p_row02_traceSegment_088_2214_0013, g32p_row02_traceSegment_088_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2241 13 14, g32p_row02_traceSegment_088_2241_0013, g32p_row02_traceSegment_088_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2214 27 27, g32p_row02_traceSegment_088_2214_0027, g32p_row02_traceSegment_088_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2160 54 54, g32p_row02_traceSegment_088_2160_0054, g32p_row02_traceSegment_088_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2268 13 14, g32p_row02_traceSegment_088_2268_0013, g32p_row02_traceSegment_088_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2295 13 14, g32p_row02_traceSegment_088_2295_0013, g32p_row02_traceSegment_088_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2268 27 27, g32p_row02_traceSegment_088_2268_0027, g32p_row02_traceSegment_088_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2322 13 14, g32p_row02_traceSegment_088_2322_0013, g32p_row02_traceSegment_088_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2349 13 14, g32p_row02_traceSegment_088_2349_0013, g32p_row02_traceSegment_088_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2322 27 27, g32p_row02_traceSegment_088_2322_0027, g32p_row02_traceSegment_088_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2268 54 54, g32p_row02_traceSegment_088_2268_0054, g32p_row02_traceSegment_088_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2160 108 108, g32p_row02_traceSegment_088_2160_0108, g32p_row02_traceSegment_088_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2376 13 14, g32p_row02_traceSegment_088_2376_0013, g32p_row02_traceSegment_088_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2403 13 14, g32p_row02_traceSegment_088_2403_0013, g32p_row02_traceSegment_088_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2376 27 27, g32p_row02_traceSegment_088_2376_0027, g32p_row02_traceSegment_088_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2430 13 14, g32p_row02_traceSegment_088_2430_0013, g32p_row02_traceSegment_088_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2457 13 14, g32p_row02_traceSegment_088_2457_0013, g32p_row02_traceSegment_088_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2430 27 27, g32p_row02_traceSegment_088_2430_0027, g32p_row02_traceSegment_088_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2376 54 54, g32p_row02_traceSegment_088_2376_0054, g32p_row02_traceSegment_088_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2484 13 14, g32p_row02_traceSegment_088_2484_0013, g32p_row02_traceSegment_088_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2511 13 14, g32p_row02_traceSegment_088_2511_0013, g32p_row02_traceSegment_088_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2484 27 27, g32p_row02_traceSegment_088_2484_0027, g32p_row02_traceSegment_088_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2538 13 14, g32p_row02_traceSegment_088_2538_0013, g32p_row02_traceSegment_088_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2565 13 14, g32p_row02_traceSegment_088_2565_0013, g32p_row02_traceSegment_088_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2538 27 27, g32p_row02_traceSegment_088_2538_0027, g32p_row02_traceSegment_088_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2484 54 54, g32p_row02_traceSegment_088_2484_0054, g32p_row02_traceSegment_088_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2376 108 108, g32p_row02_traceSegment_088_2376_0108, g32p_row02_traceSegment_088_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2160 216 216, g32p_row02_traceSegment_088_2160_0216, g32p_row02_traceSegment_088_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1728 432 432, g32p_row02_traceSegment_088_1728_0432, g32p_row02_traceSegment_088_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2592 13 14, g32p_row02_traceSegment_088_2592_0013, g32p_row02_traceSegment_088_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2619 13 14, g32p_row02_traceSegment_088_2619_0013, g32p_row02_traceSegment_088_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2592 27 27, g32p_row02_traceSegment_088_2592_0027, g32p_row02_traceSegment_088_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2646 13 14, g32p_row02_traceSegment_088_2646_0013, g32p_row02_traceSegment_088_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2673 13 14, g32p_row02_traceSegment_088_2673_0013, g32p_row02_traceSegment_088_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2646 27 27, g32p_row02_traceSegment_088_2646_0027, g32p_row02_traceSegment_088_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2592 54 54, g32p_row02_traceSegment_088_2592_0054, g32p_row02_traceSegment_088_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2700 13 14, g32p_row02_traceSegment_088_2700_0013, g32p_row02_traceSegment_088_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2727 13 14, g32p_row02_traceSegment_088_2727_0013, g32p_row02_traceSegment_088_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2700 27 27, g32p_row02_traceSegment_088_2700_0027, g32p_row02_traceSegment_088_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2754 13 14, g32p_row02_traceSegment_088_2754_0013, g32p_row02_traceSegment_088_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2781 13 14, g32p_row02_traceSegment_088_2781_0013, g32p_row02_traceSegment_088_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2754 27 27, g32p_row02_traceSegment_088_2754_0027, g32p_row02_traceSegment_088_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2700 54 54, g32p_row02_traceSegment_088_2700_0054, g32p_row02_traceSegment_088_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2592 108 108, g32p_row02_traceSegment_088_2592_0108, g32p_row02_traceSegment_088_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2808 13 14, g32p_row02_traceSegment_088_2808_0013, g32p_row02_traceSegment_088_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2835 13 14, g32p_row02_traceSegment_088_2835_0013, g32p_row02_traceSegment_088_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2808 27 27, g32p_row02_traceSegment_088_2808_0027, g32p_row02_traceSegment_088_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2862 13 14, g32p_row02_traceSegment_088_2862_0013, g32p_row02_traceSegment_088_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2889 13 14, g32p_row02_traceSegment_088_2889_0013, g32p_row02_traceSegment_088_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2862 27 27, g32p_row02_traceSegment_088_2862_0027, g32p_row02_traceSegment_088_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2808 54 54, g32p_row02_traceSegment_088_2808_0054, g32p_row02_traceSegment_088_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2916 13 14, g32p_row02_traceSegment_088_2916_0013, g32p_row02_traceSegment_088_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2943 13 14, g32p_row02_traceSegment_088_2943_0013, g32p_row02_traceSegment_088_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2916 27 27, g32p_row02_traceSegment_088_2916_0027, g32p_row02_traceSegment_088_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2970 13 14, g32p_row02_traceSegment_088_2970_0013, g32p_row02_traceSegment_088_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2997 13 14, g32p_row02_traceSegment_088_2997_0013, g32p_row02_traceSegment_088_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2970 27 27, g32p_row02_traceSegment_088_2970_0027, g32p_row02_traceSegment_088_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2916 54 54, g32p_row02_traceSegment_088_2916_0054, g32p_row02_traceSegment_088_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2808 108 108, g32p_row02_traceSegment_088_2808_0108, g32p_row02_traceSegment_088_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2592 216 216, g32p_row02_traceSegment_088_2592_0216, g32p_row02_traceSegment_088_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3024 13 14, g32p_row02_traceSegment_088_3024_0013, g32p_row02_traceSegment_088_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3051 13 14, g32p_row02_traceSegment_088_3051_0013, g32p_row02_traceSegment_088_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3024 27 27, g32p_row02_traceSegment_088_3024_0027, g32p_row02_traceSegment_088_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3078 13 14, g32p_row02_traceSegment_088_3078_0013, g32p_row02_traceSegment_088_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3118 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3105 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3105 13 14, g32p_row02_traceSegment_088_3105_0013, g32p_row02_traceSegment_088_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3078 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3078 27 27, g32p_row02_traceSegment_088_3078_0027, g32p_row02_traceSegment_088_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 3024 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3024 54 54, g32p_row02_traceSegment_088_3024_0054, g32p_row02_traceSegment_088_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3132 13 14, g32p_row02_traceSegment_088_3132_0013, g32p_row02_traceSegment_088_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3159 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3159 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3159 13 14, g32p_row02_traceSegment_088_3159_0013, g32p_row02_traceSegment_088_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3132 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3132 27 27, g32p_row02_traceSegment_088_3132_0027, g32p_row02_traceSegment_088_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3186 13 14, g32p_row02_traceSegment_088_3186_0013, g32p_row02_traceSegment_088_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3213 13 14, g32p_row02_traceSegment_088_3213_0013, g32p_row02_traceSegment_088_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3186 27 27, g32p_row02_traceSegment_088_3186_0027, g32p_row02_traceSegment_088_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3132 54 54, g32p_row02_traceSegment_088_3132_0054, g32p_row02_traceSegment_088_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 3024 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3024 108 108, g32p_row02_traceSegment_088_3024_0108, g32p_row02_traceSegment_088_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3240 13 14, g32p_row02_traceSegment_088_3240_0013, g32p_row02_traceSegment_088_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3267 13 14, g32p_row02_traceSegment_088_3267_0013, g32p_row02_traceSegment_088_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3240 27 27, g32p_row02_traceSegment_088_3240_0027, g32p_row02_traceSegment_088_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3294 13 14, g32p_row02_traceSegment_088_3294_0013, g32p_row02_traceSegment_088_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3321 13 14, g32p_row02_traceSegment_088_3321_0013, g32p_row02_traceSegment_088_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3294 27 27, g32p_row02_traceSegment_088_3294_0027, g32p_row02_traceSegment_088_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3240 54 54, g32p_row02_traceSegment_088_3240_0054, g32p_row02_traceSegment_088_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3348 13 14, g32p_row02_traceSegment_088_3348_0013, g32p_row02_traceSegment_088_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3375 13 14, g32p_row02_traceSegment_088_3375_0013, g32p_row02_traceSegment_088_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3348 27 27, g32p_row02_traceSegment_088_3348_0027, g32p_row02_traceSegment_088_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3402 13 14, g32p_row02_traceSegment_088_3402_0013, g32p_row02_traceSegment_088_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_088 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_088 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_088_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_088 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3429 13 14, g32p_row02_traceSegment_088_3429_0013, g32p_row02_traceSegment_088_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_088 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3402 27 27, g32p_row02_traceSegment_088_3402_0027, g32p_row02_traceSegment_088_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_088 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3348 54 54, g32p_row02_traceSegment_088_3348_0054, g32p_row02_traceSegment_088_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_088 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3240 108 108, g32p_row02_traceSegment_088_3240_0108, g32p_row02_traceSegment_088_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_088_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_088 3024 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 3024 216 216, g32p_row02_traceSegment_088_3024_0216, g32p_row02_traceSegment_088_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_088_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_088 2592 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 2592 432 432, g32p_row02_traceSegment_088_2592_0432, g32p_row02_traceSegment_088_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_088_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_088 1728 1728 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 1728 864 864, g32p_row02_traceSegment_088_1728_0864, g32p_row02_traceSegment_088_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_088_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_088 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_088 0 1728 1728, g32p_row02_traceSegment_088_0000_1728, g32p_row02_traceSegment_088_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_088 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 88 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_088_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_089 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 89 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_089_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 13 14, g32p_row02_traceSegment_089_0000_0013, g32p_row02_traceSegment_089_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 27 13 14, g32p_row02_traceSegment_089_0027_0013, g32p_row02_traceSegment_089_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 27 27, g32p_row02_traceSegment_089_0000_0027, g32p_row02_traceSegment_089_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 54 13 14, g32p_row02_traceSegment_089_0054_0013, g32p_row02_traceSegment_089_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 81 13 14, g32p_row02_traceSegment_089_0081_0013, g32p_row02_traceSegment_089_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 54 27 27, g32p_row02_traceSegment_089_0054_0027, g32p_row02_traceSegment_089_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 54 54, g32p_row02_traceSegment_089_0000_0054, g32p_row02_traceSegment_089_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 108 13 14, g32p_row02_traceSegment_089_0108_0013, g32p_row02_traceSegment_089_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 135 13 14, g32p_row02_traceSegment_089_0135_0013, g32p_row02_traceSegment_089_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 108 27 27, g32p_row02_traceSegment_089_0108_0027, g32p_row02_traceSegment_089_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 162 13 14, g32p_row02_traceSegment_089_0162_0013, g32p_row02_traceSegment_089_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 189 13 14, g32p_row02_traceSegment_089_0189_0013, g32p_row02_traceSegment_089_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 162 27 27, g32p_row02_traceSegment_089_0162_0027, g32p_row02_traceSegment_089_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 108 54 54, g32p_row02_traceSegment_089_0108_0054, g32p_row02_traceSegment_089_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 108 108, g32p_row02_traceSegment_089_0000_0108, g32p_row02_traceSegment_089_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 216 13 14, g32p_row02_traceSegment_089_0216_0013, g32p_row02_traceSegment_089_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 243 13 14, g32p_row02_traceSegment_089_0243_0013, g32p_row02_traceSegment_089_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 216 27 27, g32p_row02_traceSegment_089_0216_0027, g32p_row02_traceSegment_089_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 270 13 14, g32p_row02_traceSegment_089_0270_0013, g32p_row02_traceSegment_089_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 297 13 14, g32p_row02_traceSegment_089_0297_0013, g32p_row02_traceSegment_089_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 270 27 27, g32p_row02_traceSegment_089_0270_0027, g32p_row02_traceSegment_089_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 216 54 54, g32p_row02_traceSegment_089_0216_0054, g32p_row02_traceSegment_089_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 324 13 14, g32p_row02_traceSegment_089_0324_0013, g32p_row02_traceSegment_089_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 351 13 14, g32p_row02_traceSegment_089_0351_0013, g32p_row02_traceSegment_089_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 324 27 27, g32p_row02_traceSegment_089_0324_0027, g32p_row02_traceSegment_089_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 378 13 14, g32p_row02_traceSegment_089_0378_0013, g32p_row02_traceSegment_089_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 405 13 14, g32p_row02_traceSegment_089_0405_0013, g32p_row02_traceSegment_089_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 378 27 27, g32p_row02_traceSegment_089_0378_0027, g32p_row02_traceSegment_089_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 324 54 54, g32p_row02_traceSegment_089_0324_0054, g32p_row02_traceSegment_089_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 216 108 108, g32p_row02_traceSegment_089_0216_0108, g32p_row02_traceSegment_089_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 216 216, g32p_row02_traceSegment_089_0000_0216, g32p_row02_traceSegment_089_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 432 13 14, g32p_row02_traceSegment_089_0432_0013, g32p_row02_traceSegment_089_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 459 13 14, g32p_row02_traceSegment_089_0459_0013, g32p_row02_traceSegment_089_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 432 27 27, g32p_row02_traceSegment_089_0432_0027, g32p_row02_traceSegment_089_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 486 13 14, g32p_row02_traceSegment_089_0486_0013, g32p_row02_traceSegment_089_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 513 13 14, g32p_row02_traceSegment_089_0513_0013, g32p_row02_traceSegment_089_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 486 27 27, g32p_row02_traceSegment_089_0486_0027, g32p_row02_traceSegment_089_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 432 54 54, g32p_row02_traceSegment_089_0432_0054, g32p_row02_traceSegment_089_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 540 13 14, g32p_row02_traceSegment_089_0540_0013, g32p_row02_traceSegment_089_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 567 13 14, g32p_row02_traceSegment_089_0567_0013, g32p_row02_traceSegment_089_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 540 27 27, g32p_row02_traceSegment_089_0540_0027, g32p_row02_traceSegment_089_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 594 13 14, g32p_row02_traceSegment_089_0594_0013, g32p_row02_traceSegment_089_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 621 13 14, g32p_row02_traceSegment_089_0621_0013, g32p_row02_traceSegment_089_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 594 27 27, g32p_row02_traceSegment_089_0594_0027, g32p_row02_traceSegment_089_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 540 54 54, g32p_row02_traceSegment_089_0540_0054, g32p_row02_traceSegment_089_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 432 108 108, g32p_row02_traceSegment_089_0432_0108, g32p_row02_traceSegment_089_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 648 13 14, g32p_row02_traceSegment_089_0648_0013, g32p_row02_traceSegment_089_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 675 13 14, g32p_row02_traceSegment_089_0675_0013, g32p_row02_traceSegment_089_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 648 27 27, g32p_row02_traceSegment_089_0648_0027, g32p_row02_traceSegment_089_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 702 13 14, g32p_row02_traceSegment_089_0702_0013, g32p_row02_traceSegment_089_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 729 13 14, g32p_row02_traceSegment_089_0729_0013, g32p_row02_traceSegment_089_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 702 27 27, g32p_row02_traceSegment_089_0702_0027, g32p_row02_traceSegment_089_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 648 54 54, g32p_row02_traceSegment_089_0648_0054, g32p_row02_traceSegment_089_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 756 13 14, g32p_row02_traceSegment_089_0756_0013, g32p_row02_traceSegment_089_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 783 13 14, g32p_row02_traceSegment_089_0783_0013, g32p_row02_traceSegment_089_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 756 27 27, g32p_row02_traceSegment_089_0756_0027, g32p_row02_traceSegment_089_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 810 13 14, g32p_row02_traceSegment_089_0810_0013, g32p_row02_traceSegment_089_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 837 13 14, g32p_row02_traceSegment_089_0837_0013, g32p_row02_traceSegment_089_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 810 27 27, g32p_row02_traceSegment_089_0810_0027, g32p_row02_traceSegment_089_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 756 54 54, g32p_row02_traceSegment_089_0756_0054, g32p_row02_traceSegment_089_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 648 108 108, g32p_row02_traceSegment_089_0648_0108, g32p_row02_traceSegment_089_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 432 216 216, g32p_row02_traceSegment_089_0432_0216, g32p_row02_traceSegment_089_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_089 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 432 432, g32p_row02_traceSegment_089_0000_0432, g32p_row02_traceSegment_089_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 864 13 14, g32p_row02_traceSegment_089_0864_0013, g32p_row02_traceSegment_089_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 891 13 14, g32p_row02_traceSegment_089_0891_0013, g32p_row02_traceSegment_089_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 864 27 27, g32p_row02_traceSegment_089_0864_0027, g32p_row02_traceSegment_089_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 918 13 14, g32p_row02_traceSegment_089_0918_0013, g32p_row02_traceSegment_089_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 945 13 14, g32p_row02_traceSegment_089_0945_0013, g32p_row02_traceSegment_089_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 918 27 27, g32p_row02_traceSegment_089_0918_0027, g32p_row02_traceSegment_089_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 864 54 54, g32p_row02_traceSegment_089_0864_0054, g32p_row02_traceSegment_089_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 972 13 14, g32p_row02_traceSegment_089_0972_0013, g32p_row02_traceSegment_089_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 999 13 14, g32p_row02_traceSegment_089_0999_0013, g32p_row02_traceSegment_089_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 972 27 27, g32p_row02_traceSegment_089_0972_0027, g32p_row02_traceSegment_089_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1026 13 14, g32p_row02_traceSegment_089_1026_0013, g32p_row02_traceSegment_089_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1053 13 14, g32p_row02_traceSegment_089_1053_0013, g32p_row02_traceSegment_089_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1026 27 27, g32p_row02_traceSegment_089_1026_0027, g32p_row02_traceSegment_089_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 972 54 54, g32p_row02_traceSegment_089_0972_0054, g32p_row02_traceSegment_089_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 864 108 108, g32p_row02_traceSegment_089_0864_0108, g32p_row02_traceSegment_089_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1080 13 14, g32p_row02_traceSegment_089_1080_0013, g32p_row02_traceSegment_089_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1107 13 14, g32p_row02_traceSegment_089_1107_0013, g32p_row02_traceSegment_089_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1080 27 27, g32p_row02_traceSegment_089_1080_0027, g32p_row02_traceSegment_089_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1134 13 14, g32p_row02_traceSegment_089_1134_0013, g32p_row02_traceSegment_089_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1161 13 14, g32p_row02_traceSegment_089_1161_0013, g32p_row02_traceSegment_089_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1134 27 27, g32p_row02_traceSegment_089_1134_0027, g32p_row02_traceSegment_089_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1080 54 54, g32p_row02_traceSegment_089_1080_0054, g32p_row02_traceSegment_089_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1188 13 14, g32p_row02_traceSegment_089_1188_0013, g32p_row02_traceSegment_089_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1215 13 14, g32p_row02_traceSegment_089_1215_0013, g32p_row02_traceSegment_089_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1188 27 27, g32p_row02_traceSegment_089_1188_0027, g32p_row02_traceSegment_089_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1242 13 14, g32p_row02_traceSegment_089_1242_0013, g32p_row02_traceSegment_089_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1269 13 14, g32p_row02_traceSegment_089_1269_0013, g32p_row02_traceSegment_089_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1242 27 27, g32p_row02_traceSegment_089_1242_0027, g32p_row02_traceSegment_089_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1188 54 54, g32p_row02_traceSegment_089_1188_0054, g32p_row02_traceSegment_089_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1080 108 108, g32p_row02_traceSegment_089_1080_0108, g32p_row02_traceSegment_089_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 864 216 216, g32p_row02_traceSegment_089_0864_0216, g32p_row02_traceSegment_089_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1296 13 14, g32p_row02_traceSegment_089_1296_0013, g32p_row02_traceSegment_089_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1323 13 14, g32p_row02_traceSegment_089_1323_0013, g32p_row02_traceSegment_089_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1296 27 27, g32p_row02_traceSegment_089_1296_0027, g32p_row02_traceSegment_089_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1350 13 14, g32p_row02_traceSegment_089_1350_0013, g32p_row02_traceSegment_089_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1377 13 14, g32p_row02_traceSegment_089_1377_0013, g32p_row02_traceSegment_089_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1350 27 27, g32p_row02_traceSegment_089_1350_0027, g32p_row02_traceSegment_089_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1296 54 54, g32p_row02_traceSegment_089_1296_0054, g32p_row02_traceSegment_089_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1404 13 14, g32p_row02_traceSegment_089_1404_0013, g32p_row02_traceSegment_089_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1431 13 14, g32p_row02_traceSegment_089_1431_0013, g32p_row02_traceSegment_089_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1404 27 27, g32p_row02_traceSegment_089_1404_0027, g32p_row02_traceSegment_089_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1458 13 14, g32p_row02_traceSegment_089_1458_0013, g32p_row02_traceSegment_089_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1485 13 14, g32p_row02_traceSegment_089_1485_0013, g32p_row02_traceSegment_089_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1458 27 27, g32p_row02_traceSegment_089_1458_0027, g32p_row02_traceSegment_089_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1404 54 54, g32p_row02_traceSegment_089_1404_0054, g32p_row02_traceSegment_089_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1296 108 108, g32p_row02_traceSegment_089_1296_0108, g32p_row02_traceSegment_089_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1512 13 14, g32p_row02_traceSegment_089_1512_0013, g32p_row02_traceSegment_089_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1539 13 14, g32p_row02_traceSegment_089_1539_0013, g32p_row02_traceSegment_089_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1512 27 27, g32p_row02_traceSegment_089_1512_0027, g32p_row02_traceSegment_089_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1566 13 14, g32p_row02_traceSegment_089_1566_0013, g32p_row02_traceSegment_089_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1593 13 14, g32p_row02_traceSegment_089_1593_0013, g32p_row02_traceSegment_089_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1566 27 27, g32p_row02_traceSegment_089_1566_0027, g32p_row02_traceSegment_089_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1512 54 54, g32p_row02_traceSegment_089_1512_0054, g32p_row02_traceSegment_089_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1620 13 14, g32p_row02_traceSegment_089_1620_0013, g32p_row02_traceSegment_089_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1647 13 14, g32p_row02_traceSegment_089_1647_0013, g32p_row02_traceSegment_089_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1620 27 27, g32p_row02_traceSegment_089_1620_0027, g32p_row02_traceSegment_089_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1674 13 14, g32p_row02_traceSegment_089_1674_0013, g32p_row02_traceSegment_089_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1701 13 14, g32p_row02_traceSegment_089_1701_0013, g32p_row02_traceSegment_089_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1674 27 27, g32p_row02_traceSegment_089_1674_0027, g32p_row02_traceSegment_089_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1620 54 54, g32p_row02_traceSegment_089_1620_0054, g32p_row02_traceSegment_089_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1512 108 108, g32p_row02_traceSegment_089_1512_0108, g32p_row02_traceSegment_089_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1296 216 216, g32p_row02_traceSegment_089_1296_0216, g32p_row02_traceSegment_089_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_089 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 864 432 432, g32p_row02_traceSegment_089_0864_0432, g32p_row02_traceSegment_089_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_089 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 864 864, g32p_row02_traceSegment_089_0000_0864, g32p_row02_traceSegment_089_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1728 13 14, g32p_row02_traceSegment_089_1728_0013, g32p_row02_traceSegment_089_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1755 13 14, g32p_row02_traceSegment_089_1755_0013, g32p_row02_traceSegment_089_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1728 27 27, g32p_row02_traceSegment_089_1728_0027, g32p_row02_traceSegment_089_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1782 13 14, g32p_row02_traceSegment_089_1782_0013, g32p_row02_traceSegment_089_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1809 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1809 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1809 13 14, g32p_row02_traceSegment_089_1809_0013, g32p_row02_traceSegment_089_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1782 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1782 27 27, g32p_row02_traceSegment_089_1782_0027, g32p_row02_traceSegment_089_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1728 54 54, g32p_row02_traceSegment_089_1728_0054, g32p_row02_traceSegment_089_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1836 13 14, g32p_row02_traceSegment_089_1836_0013, g32p_row02_traceSegment_089_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1863 13 14, g32p_row02_traceSegment_089_1863_0013, g32p_row02_traceSegment_089_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1836 27 27, g32p_row02_traceSegment_089_1836_0027, g32p_row02_traceSegment_089_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1890 13 14, g32p_row02_traceSegment_089_1890_0013, g32p_row02_traceSegment_089_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1917 13 14, g32p_row02_traceSegment_089_1917_0013, g32p_row02_traceSegment_089_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1890 27 27, g32p_row02_traceSegment_089_1890_0027, g32p_row02_traceSegment_089_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1836 54 54, g32p_row02_traceSegment_089_1836_0054, g32p_row02_traceSegment_089_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1728 108 108, g32p_row02_traceSegment_089_1728_0108, g32p_row02_traceSegment_089_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1944 13 14, g32p_row02_traceSegment_089_1944_0013, g32p_row02_traceSegment_089_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1971 13 14, g32p_row02_traceSegment_089_1971_0013, g32p_row02_traceSegment_089_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1944 27 27, g32p_row02_traceSegment_089_1944_0027, g32p_row02_traceSegment_089_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1998 13 14, g32p_row02_traceSegment_089_1998_0013, g32p_row02_traceSegment_089_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2025 13 14, g32p_row02_traceSegment_089_2025_0013, g32p_row02_traceSegment_089_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1998 27 27, g32p_row02_traceSegment_089_1998_0027, g32p_row02_traceSegment_089_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1944 54 54, g32p_row02_traceSegment_089_1944_0054, g32p_row02_traceSegment_089_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2052 13 14, g32p_row02_traceSegment_089_2052_0013, g32p_row02_traceSegment_089_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2079 13 14, g32p_row02_traceSegment_089_2079_0013, g32p_row02_traceSegment_089_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2052 27 27, g32p_row02_traceSegment_089_2052_0027, g32p_row02_traceSegment_089_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2106 13 14, g32p_row02_traceSegment_089_2106_0013, g32p_row02_traceSegment_089_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2133 13 14, g32p_row02_traceSegment_089_2133_0013, g32p_row02_traceSegment_089_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2106 27 27, g32p_row02_traceSegment_089_2106_0027, g32p_row02_traceSegment_089_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2052 54 54, g32p_row02_traceSegment_089_2052_0054, g32p_row02_traceSegment_089_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1944 108 108, g32p_row02_traceSegment_089_1944_0108, g32p_row02_traceSegment_089_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1728 216 216, g32p_row02_traceSegment_089_1728_0216, g32p_row02_traceSegment_089_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2173 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2160 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2160 13 14, g32p_row02_traceSegment_089_2160_0013, g32p_row02_traceSegment_089_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2187 13 14, g32p_row02_traceSegment_089_2187_0013, g32p_row02_traceSegment_089_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2160 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2160 27 27, g32p_row02_traceSegment_089_2160_0027, g32p_row02_traceSegment_089_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2227 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2214 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2214 13 14, g32p_row02_traceSegment_089_2214_0013, g32p_row02_traceSegment_089_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2241 13 14, g32p_row02_traceSegment_089_2241_0013, g32p_row02_traceSegment_089_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2214 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2214 27 27, g32p_row02_traceSegment_089_2214_0027, g32p_row02_traceSegment_089_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2160 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2160 54 54, g32p_row02_traceSegment_089_2160_0054, g32p_row02_traceSegment_089_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2268 13 14, g32p_row02_traceSegment_089_2268_0013, g32p_row02_traceSegment_089_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2295 13 14, g32p_row02_traceSegment_089_2295_0013, g32p_row02_traceSegment_089_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2268 27 27, g32p_row02_traceSegment_089_2268_0027, g32p_row02_traceSegment_089_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2322 13 14, g32p_row02_traceSegment_089_2322_0013, g32p_row02_traceSegment_089_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2349 13 14, g32p_row02_traceSegment_089_2349_0013, g32p_row02_traceSegment_089_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2322 27 27, g32p_row02_traceSegment_089_2322_0027, g32p_row02_traceSegment_089_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2268 54 54, g32p_row02_traceSegment_089_2268_0054, g32p_row02_traceSegment_089_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 2160 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2160 108 108, g32p_row02_traceSegment_089_2160_0108, g32p_row02_traceSegment_089_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2376 13 14, g32p_row02_traceSegment_089_2376_0013, g32p_row02_traceSegment_089_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2403 13 14, g32p_row02_traceSegment_089_2403_0013, g32p_row02_traceSegment_089_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2376 27 27, g32p_row02_traceSegment_089_2376_0027, g32p_row02_traceSegment_089_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2430 13 14, g32p_row02_traceSegment_089_2430_0013, g32p_row02_traceSegment_089_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2457 13 14, g32p_row02_traceSegment_089_2457_0013, g32p_row02_traceSegment_089_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2430 27 27, g32p_row02_traceSegment_089_2430_0027, g32p_row02_traceSegment_089_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2376 54 54, g32p_row02_traceSegment_089_2376_0054, g32p_row02_traceSegment_089_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2484 13 14, g32p_row02_traceSegment_089_2484_0013, g32p_row02_traceSegment_089_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2511 13 14, g32p_row02_traceSegment_089_2511_0013, g32p_row02_traceSegment_089_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2484 27 27, g32p_row02_traceSegment_089_2484_0027, g32p_row02_traceSegment_089_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2538 13 14, g32p_row02_traceSegment_089_2538_0013, g32p_row02_traceSegment_089_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2565 13 14, g32p_row02_traceSegment_089_2565_0013, g32p_row02_traceSegment_089_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2538 27 27, g32p_row02_traceSegment_089_2538_0027, g32p_row02_traceSegment_089_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2484 54 54, g32p_row02_traceSegment_089_2484_0054, g32p_row02_traceSegment_089_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2376 108 108, g32p_row02_traceSegment_089_2376_0108, g32p_row02_traceSegment_089_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 2160 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2160 216 216, g32p_row02_traceSegment_089_2160_0216, g32p_row02_traceSegment_089_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1728 432 432, g32p_row02_traceSegment_089_1728_0432, g32p_row02_traceSegment_089_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2592 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2592 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2592 13 14, g32p_row02_traceSegment_089_2592_0013, g32p_row02_traceSegment_089_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2632 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2619 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2619 13 14, g32p_row02_traceSegment_089_2619_0013, g32p_row02_traceSegment_089_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2592 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2592 27 27, g32p_row02_traceSegment_089_2592_0027, g32p_row02_traceSegment_089_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2646 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2646 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2646 13 14, g32p_row02_traceSegment_089_2646_0013, g32p_row02_traceSegment_089_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2673 13 14, g32p_row02_traceSegment_089_2673_0013, g32p_row02_traceSegment_089_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2646 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2646 27 27, g32p_row02_traceSegment_089_2646_0027, g32p_row02_traceSegment_089_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2592 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2592 54 54, g32p_row02_traceSegment_089_2592_0054, g32p_row02_traceSegment_089_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2700 13 14, g32p_row02_traceSegment_089_2700_0013, g32p_row02_traceSegment_089_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2727 13 14, g32p_row02_traceSegment_089_2727_0013, g32p_row02_traceSegment_089_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2700 27 27, g32p_row02_traceSegment_089_2700_0027, g32p_row02_traceSegment_089_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2754 13 14, g32p_row02_traceSegment_089_2754_0013, g32p_row02_traceSegment_089_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2781 13 14, g32p_row02_traceSegment_089_2781_0013, g32p_row02_traceSegment_089_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2754 27 27, g32p_row02_traceSegment_089_2754_0027, g32p_row02_traceSegment_089_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2700 54 54, g32p_row02_traceSegment_089_2700_0054, g32p_row02_traceSegment_089_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 2592 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2592 108 108, g32p_row02_traceSegment_089_2592_0108, g32p_row02_traceSegment_089_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2808 13 14, g32p_row02_traceSegment_089_2808_0013, g32p_row02_traceSegment_089_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2848 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2835 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2835 13 14, g32p_row02_traceSegment_089_2835_0013, g32p_row02_traceSegment_089_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2808 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2808 27 27, g32p_row02_traceSegment_089_2808_0027, g32p_row02_traceSegment_089_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2862 13 14, g32p_row02_traceSegment_089_2862_0013, g32p_row02_traceSegment_089_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2889 13 14, g32p_row02_traceSegment_089_2889_0013, g32p_row02_traceSegment_089_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2862 27 27, g32p_row02_traceSegment_089_2862_0027, g32p_row02_traceSegment_089_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2808 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2808 54 54, g32p_row02_traceSegment_089_2808_0054, g32p_row02_traceSegment_089_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2916 13 14, g32p_row02_traceSegment_089_2916_0013, g32p_row02_traceSegment_089_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2943 13 14, g32p_row02_traceSegment_089_2943_0013, g32p_row02_traceSegment_089_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2916 27 27, g32p_row02_traceSegment_089_2916_0027, g32p_row02_traceSegment_089_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2970 13 14, g32p_row02_traceSegment_089_2970_0013, g32p_row02_traceSegment_089_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2997 13 14, g32p_row02_traceSegment_089_2997_0013, g32p_row02_traceSegment_089_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2970 27 27, g32p_row02_traceSegment_089_2970_0027, g32p_row02_traceSegment_089_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2916 54 54, g32p_row02_traceSegment_089_2916_0054, g32p_row02_traceSegment_089_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 2808 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2808 108 108, g32p_row02_traceSegment_089_2808_0108, g32p_row02_traceSegment_089_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 2592 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2592 216 216, g32p_row02_traceSegment_089_2592_0216, g32p_row02_traceSegment_089_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3024 13 14, g32p_row02_traceSegment_089_3024_0013, g32p_row02_traceSegment_089_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3051 13 14, g32p_row02_traceSegment_089_3051_0013, g32p_row02_traceSegment_089_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3024 27 27, g32p_row02_traceSegment_089_3024_0027, g32p_row02_traceSegment_089_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3078 13 14, g32p_row02_traceSegment_089_3078_0013, g32p_row02_traceSegment_089_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3105 13 14, g32p_row02_traceSegment_089_3105_0013, g32p_row02_traceSegment_089_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3078 27 27, g32p_row02_traceSegment_089_3078_0027, g32p_row02_traceSegment_089_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3024 54 54, g32p_row02_traceSegment_089_3024_0054, g32p_row02_traceSegment_089_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3132 13 14, g32p_row02_traceSegment_089_3132_0013, g32p_row02_traceSegment_089_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3159 13 14, g32p_row02_traceSegment_089_3159_0013, g32p_row02_traceSegment_089_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3132 27 27, g32p_row02_traceSegment_089_3132_0027, g32p_row02_traceSegment_089_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3186 13 14, g32p_row02_traceSegment_089_3186_0013, g32p_row02_traceSegment_089_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3213 13 14, g32p_row02_traceSegment_089_3213_0013, g32p_row02_traceSegment_089_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3186 27 27, g32p_row02_traceSegment_089_3186_0027, g32p_row02_traceSegment_089_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3132 54 54, g32p_row02_traceSegment_089_3132_0054, g32p_row02_traceSegment_089_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3024 108 108, g32p_row02_traceSegment_089_3024_0108, g32p_row02_traceSegment_089_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3240 13 14, g32p_row02_traceSegment_089_3240_0013, g32p_row02_traceSegment_089_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3267 13 14, g32p_row02_traceSegment_089_3267_0013, g32p_row02_traceSegment_089_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3240 27 27, g32p_row02_traceSegment_089_3240_0027, g32p_row02_traceSegment_089_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3294 13 14, g32p_row02_traceSegment_089_3294_0013, g32p_row02_traceSegment_089_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3321 13 14, g32p_row02_traceSegment_089_3321_0013, g32p_row02_traceSegment_089_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3294 27 27, g32p_row02_traceSegment_089_3294_0027, g32p_row02_traceSegment_089_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3240 54 54, g32p_row02_traceSegment_089_3240_0054, g32p_row02_traceSegment_089_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3348 13 14, g32p_row02_traceSegment_089_3348_0013, g32p_row02_traceSegment_089_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3375 13 14, g32p_row02_traceSegment_089_3375_0013, g32p_row02_traceSegment_089_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3348 27 27, g32p_row02_traceSegment_089_3348_0027, g32p_row02_traceSegment_089_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3402 13 14, g32p_row02_traceSegment_089_3402_0013, g32p_row02_traceSegment_089_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_089 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_089 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_089_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_089 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3429 13 14, g32p_row02_traceSegment_089_3429_0013, g32p_row02_traceSegment_089_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_089 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3402 27 27, g32p_row02_traceSegment_089_3402_0027, g32p_row02_traceSegment_089_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_089 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3348 54 54, g32p_row02_traceSegment_089_3348_0054, g32p_row02_traceSegment_089_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_089 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3240 108 108, g32p_row02_traceSegment_089_3240_0108, g32p_row02_traceSegment_089_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_089_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_089 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 3024 216 216, g32p_row02_traceSegment_089_3024_0216, g32p_row02_traceSegment_089_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_089_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_089 2592 864 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 2592 432 432, g32p_row02_traceSegment_089_2592_0432, g32p_row02_traceSegment_089_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_089_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_089 1728 1728 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 1728 864 864, g32p_row02_traceSegment_089_1728_0864, g32p_row02_traceSegment_089_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_089_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_089 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_089 0 1728 1728, g32p_row02_traceSegment_089_0000_1728, g32p_row02_traceSegment_089_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_089 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 89 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_089_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_082 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 82) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 82) (g32p_literalTraceValue 1 82)
      [1, -1, 1] [0, 0, 41472, 41472] = true := by
  rw [g32p_row02_traceCoefficients_082]
  decide +kernel

theorem g32p_row02_tracePolynomial_083 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 83) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 83) (g32p_literalTraceValue 1 83)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_083]
  decide +kernel

theorem g32p_row02_tracePolynomial_084 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 84) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 84) (g32p_literalTraceValue 1 84)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_084]
  decide +kernel

theorem g32p_row02_tracePolynomial_085 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 85) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 85) (g32p_literalTraceValue 1 85)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_085]
  decide +kernel

theorem g32p_row02_tracePolynomial_086 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 86) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 86) (g32p_literalTraceValue 1 86)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_086]
  decide +kernel

theorem g32p_row02_tracePolynomial_087 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 87) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 87) (g32p_literalTraceValue 1 87)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_087]
  decide +kernel

theorem g32p_row02_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 88) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 88) (g32p_literalTraceValue 1 88)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_088]
  decide +kernel

theorem g32p_row02_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 89) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 89) (g32p_literalTraceValue 1 89)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_089]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
