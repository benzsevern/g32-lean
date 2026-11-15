import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_051 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 51 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_051_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 13 14, g32p_row02_traceSegment_051_0000_0013, g32p_row02_traceSegment_051_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 27 13 14, g32p_row02_traceSegment_051_0027_0013, g32p_row02_traceSegment_051_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 27 27, g32p_row02_traceSegment_051_0000_0027, g32p_row02_traceSegment_051_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 54 13 14, g32p_row02_traceSegment_051_0054_0013, g32p_row02_traceSegment_051_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 81 13 14, g32p_row02_traceSegment_051_0081_0013, g32p_row02_traceSegment_051_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 54 27 27, g32p_row02_traceSegment_051_0054_0027, g32p_row02_traceSegment_051_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 54 54, g32p_row02_traceSegment_051_0000_0054, g32p_row02_traceSegment_051_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 108 13 14, g32p_row02_traceSegment_051_0108_0013, g32p_row02_traceSegment_051_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 135 13 14, g32p_row02_traceSegment_051_0135_0013, g32p_row02_traceSegment_051_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 108 27 27, g32p_row02_traceSegment_051_0108_0027, g32p_row02_traceSegment_051_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 162 13 14, g32p_row02_traceSegment_051_0162_0013, g32p_row02_traceSegment_051_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 189 13 14, g32p_row02_traceSegment_051_0189_0013, g32p_row02_traceSegment_051_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 162 27 27, g32p_row02_traceSegment_051_0162_0027, g32p_row02_traceSegment_051_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 108 54 54, g32p_row02_traceSegment_051_0108_0054, g32p_row02_traceSegment_051_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 108 108, g32p_row02_traceSegment_051_0000_0108, g32p_row02_traceSegment_051_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 216 13 14, g32p_row02_traceSegment_051_0216_0013, g32p_row02_traceSegment_051_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 243 13 14, g32p_row02_traceSegment_051_0243_0013, g32p_row02_traceSegment_051_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 216 27 27, g32p_row02_traceSegment_051_0216_0027, g32p_row02_traceSegment_051_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 270 13 14, g32p_row02_traceSegment_051_0270_0013, g32p_row02_traceSegment_051_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 297 13 14, g32p_row02_traceSegment_051_0297_0013, g32p_row02_traceSegment_051_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 270 27 27, g32p_row02_traceSegment_051_0270_0027, g32p_row02_traceSegment_051_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 216 54 54, g32p_row02_traceSegment_051_0216_0054, g32p_row02_traceSegment_051_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 324 13 14, g32p_row02_traceSegment_051_0324_0013, g32p_row02_traceSegment_051_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 351 13 14, g32p_row02_traceSegment_051_0351_0013, g32p_row02_traceSegment_051_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 324 27 27, g32p_row02_traceSegment_051_0324_0027, g32p_row02_traceSegment_051_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 378 13 14, g32p_row02_traceSegment_051_0378_0013, g32p_row02_traceSegment_051_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 405 13 14, g32p_row02_traceSegment_051_0405_0013, g32p_row02_traceSegment_051_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 378 27 27, g32p_row02_traceSegment_051_0378_0027, g32p_row02_traceSegment_051_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 324 54 54, g32p_row02_traceSegment_051_0324_0054, g32p_row02_traceSegment_051_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 216 108 108, g32p_row02_traceSegment_051_0216_0108, g32p_row02_traceSegment_051_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 216 216, g32p_row02_traceSegment_051_0000_0216, g32p_row02_traceSegment_051_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 432 13 14, g32p_row02_traceSegment_051_0432_0013, g32p_row02_traceSegment_051_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 459 13 14, g32p_row02_traceSegment_051_0459_0013, g32p_row02_traceSegment_051_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 432 27 27, g32p_row02_traceSegment_051_0432_0027, g32p_row02_traceSegment_051_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 486 13 14, g32p_row02_traceSegment_051_0486_0013, g32p_row02_traceSegment_051_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 513 13 14, g32p_row02_traceSegment_051_0513_0013, g32p_row02_traceSegment_051_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 486 27 27, g32p_row02_traceSegment_051_0486_0027, g32p_row02_traceSegment_051_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 432 54 54, g32p_row02_traceSegment_051_0432_0054, g32p_row02_traceSegment_051_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 540 13 14, g32p_row02_traceSegment_051_0540_0013, g32p_row02_traceSegment_051_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 567 13 14, g32p_row02_traceSegment_051_0567_0013, g32p_row02_traceSegment_051_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 540 27 27, g32p_row02_traceSegment_051_0540_0027, g32p_row02_traceSegment_051_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 594 13 14, g32p_row02_traceSegment_051_0594_0013, g32p_row02_traceSegment_051_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 621 13 14, g32p_row02_traceSegment_051_0621_0013, g32p_row02_traceSegment_051_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 594 27 27, g32p_row02_traceSegment_051_0594_0027, g32p_row02_traceSegment_051_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 540 54 54, g32p_row02_traceSegment_051_0540_0054, g32p_row02_traceSegment_051_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 432 108 108, g32p_row02_traceSegment_051_0432_0108, g32p_row02_traceSegment_051_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 648 13 14, g32p_row02_traceSegment_051_0648_0013, g32p_row02_traceSegment_051_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 675 13 14, g32p_row02_traceSegment_051_0675_0013, g32p_row02_traceSegment_051_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 648 27 27, g32p_row02_traceSegment_051_0648_0027, g32p_row02_traceSegment_051_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 702 13 14, g32p_row02_traceSegment_051_0702_0013, g32p_row02_traceSegment_051_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 729 13 14, g32p_row02_traceSegment_051_0729_0013, g32p_row02_traceSegment_051_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 702 27 27, g32p_row02_traceSegment_051_0702_0027, g32p_row02_traceSegment_051_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 648 54 54, g32p_row02_traceSegment_051_0648_0054, g32p_row02_traceSegment_051_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 756 13 14, g32p_row02_traceSegment_051_0756_0013, g32p_row02_traceSegment_051_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 783 13 14, g32p_row02_traceSegment_051_0783_0013, g32p_row02_traceSegment_051_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 756 27 27, g32p_row02_traceSegment_051_0756_0027, g32p_row02_traceSegment_051_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 810 13 14, g32p_row02_traceSegment_051_0810_0013, g32p_row02_traceSegment_051_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 837 13 14, g32p_row02_traceSegment_051_0837_0013, g32p_row02_traceSegment_051_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 810 27 27, g32p_row02_traceSegment_051_0810_0027, g32p_row02_traceSegment_051_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 756 54 54, g32p_row02_traceSegment_051_0756_0054, g32p_row02_traceSegment_051_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 648 108 108, g32p_row02_traceSegment_051_0648_0108, g32p_row02_traceSegment_051_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 432 216 216, g32p_row02_traceSegment_051_0432_0216, g32p_row02_traceSegment_051_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_051 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 432 432, g32p_row02_traceSegment_051_0000_0432, g32p_row02_traceSegment_051_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 864 13 14, g32p_row02_traceSegment_051_0864_0013, g32p_row02_traceSegment_051_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 891 13 14, g32p_row02_traceSegment_051_0891_0013, g32p_row02_traceSegment_051_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 864 27 27, g32p_row02_traceSegment_051_0864_0027, g32p_row02_traceSegment_051_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 918 13 14, g32p_row02_traceSegment_051_0918_0013, g32p_row02_traceSegment_051_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 945 13 14, g32p_row02_traceSegment_051_0945_0013, g32p_row02_traceSegment_051_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 918 27 27, g32p_row02_traceSegment_051_0918_0027, g32p_row02_traceSegment_051_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 864 54 54, g32p_row02_traceSegment_051_0864_0054, g32p_row02_traceSegment_051_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 972 13 14, g32p_row02_traceSegment_051_0972_0013, g32p_row02_traceSegment_051_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 999 13 14, g32p_row02_traceSegment_051_0999_0013, g32p_row02_traceSegment_051_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 972 27 27, g32p_row02_traceSegment_051_0972_0027, g32p_row02_traceSegment_051_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1026 13 14, g32p_row02_traceSegment_051_1026_0013, g32p_row02_traceSegment_051_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1053 13 14, g32p_row02_traceSegment_051_1053_0013, g32p_row02_traceSegment_051_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1026 27 27, g32p_row02_traceSegment_051_1026_0027, g32p_row02_traceSegment_051_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 972 54 54, g32p_row02_traceSegment_051_0972_0054, g32p_row02_traceSegment_051_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 864 108 108, g32p_row02_traceSegment_051_0864_0108, g32p_row02_traceSegment_051_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1080 13 14, g32p_row02_traceSegment_051_1080_0013, g32p_row02_traceSegment_051_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1107 13 14, g32p_row02_traceSegment_051_1107_0013, g32p_row02_traceSegment_051_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1080 27 27, g32p_row02_traceSegment_051_1080_0027, g32p_row02_traceSegment_051_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1134 13 14, g32p_row02_traceSegment_051_1134_0013, g32p_row02_traceSegment_051_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1161 13 14, g32p_row02_traceSegment_051_1161_0013, g32p_row02_traceSegment_051_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1134 27 27, g32p_row02_traceSegment_051_1134_0027, g32p_row02_traceSegment_051_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1080 54 54, g32p_row02_traceSegment_051_1080_0054, g32p_row02_traceSegment_051_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1188 13 14, g32p_row02_traceSegment_051_1188_0013, g32p_row02_traceSegment_051_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1215 13 14, g32p_row02_traceSegment_051_1215_0013, g32p_row02_traceSegment_051_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1188 27 27, g32p_row02_traceSegment_051_1188_0027, g32p_row02_traceSegment_051_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1242 13 14, g32p_row02_traceSegment_051_1242_0013, g32p_row02_traceSegment_051_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1269 13 14, g32p_row02_traceSegment_051_1269_0013, g32p_row02_traceSegment_051_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1242 27 27, g32p_row02_traceSegment_051_1242_0027, g32p_row02_traceSegment_051_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1188 54 54, g32p_row02_traceSegment_051_1188_0054, g32p_row02_traceSegment_051_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1080 108 108, g32p_row02_traceSegment_051_1080_0108, g32p_row02_traceSegment_051_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 864 216 216, g32p_row02_traceSegment_051_0864_0216, g32p_row02_traceSegment_051_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1296 13 14, g32p_row02_traceSegment_051_1296_0013, g32p_row02_traceSegment_051_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1323 13 14, g32p_row02_traceSegment_051_1323_0013, g32p_row02_traceSegment_051_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1296 27 27, g32p_row02_traceSegment_051_1296_0027, g32p_row02_traceSegment_051_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1350 13 14, g32p_row02_traceSegment_051_1350_0013, g32p_row02_traceSegment_051_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1377 13 14, g32p_row02_traceSegment_051_1377_0013, g32p_row02_traceSegment_051_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1350 27 27, g32p_row02_traceSegment_051_1350_0027, g32p_row02_traceSegment_051_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1296 54 54, g32p_row02_traceSegment_051_1296_0054, g32p_row02_traceSegment_051_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1404 13 14, g32p_row02_traceSegment_051_1404_0013, g32p_row02_traceSegment_051_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1431 13 14, g32p_row02_traceSegment_051_1431_0013, g32p_row02_traceSegment_051_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1404 27 27, g32p_row02_traceSegment_051_1404_0027, g32p_row02_traceSegment_051_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1458 13 14, g32p_row02_traceSegment_051_1458_0013, g32p_row02_traceSegment_051_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1485 13 14, g32p_row02_traceSegment_051_1485_0013, g32p_row02_traceSegment_051_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1458 27 27, g32p_row02_traceSegment_051_1458_0027, g32p_row02_traceSegment_051_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1404 54 54, g32p_row02_traceSegment_051_1404_0054, g32p_row02_traceSegment_051_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1296 108 108, g32p_row02_traceSegment_051_1296_0108, g32p_row02_traceSegment_051_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1512 13 14, g32p_row02_traceSegment_051_1512_0013, g32p_row02_traceSegment_051_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1539 13 14, g32p_row02_traceSegment_051_1539_0013, g32p_row02_traceSegment_051_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1512 27 27, g32p_row02_traceSegment_051_1512_0027, g32p_row02_traceSegment_051_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1566 13 14, g32p_row02_traceSegment_051_1566_0013, g32p_row02_traceSegment_051_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1593 13 14, g32p_row02_traceSegment_051_1593_0013, g32p_row02_traceSegment_051_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1566 27 27, g32p_row02_traceSegment_051_1566_0027, g32p_row02_traceSegment_051_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1512 54 54, g32p_row02_traceSegment_051_1512_0054, g32p_row02_traceSegment_051_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1620 13 14, g32p_row02_traceSegment_051_1620_0013, g32p_row02_traceSegment_051_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1647 13 14, g32p_row02_traceSegment_051_1647_0013, g32p_row02_traceSegment_051_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1620 27 27, g32p_row02_traceSegment_051_1620_0027, g32p_row02_traceSegment_051_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1674 13 14, g32p_row02_traceSegment_051_1674_0013, g32p_row02_traceSegment_051_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1701 13 14, g32p_row02_traceSegment_051_1701_0013, g32p_row02_traceSegment_051_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1674 27 27, g32p_row02_traceSegment_051_1674_0027, g32p_row02_traceSegment_051_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1620 54 54, g32p_row02_traceSegment_051_1620_0054, g32p_row02_traceSegment_051_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1512 108 108, g32p_row02_traceSegment_051_1512_0108, g32p_row02_traceSegment_051_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1296 216 216, g32p_row02_traceSegment_051_1296_0216, g32p_row02_traceSegment_051_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_051 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 864 432 432, g32p_row02_traceSegment_051_0864_0432, g32p_row02_traceSegment_051_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_051 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 864 864, g32p_row02_traceSegment_051_0000_0864, g32p_row02_traceSegment_051_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1728 13 14, g32p_row02_traceSegment_051_1728_0013, g32p_row02_traceSegment_051_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1755 13 14, g32p_row02_traceSegment_051_1755_0013, g32p_row02_traceSegment_051_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1728 27 27, g32p_row02_traceSegment_051_1728_0027, g32p_row02_traceSegment_051_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1782 13 14, g32p_row02_traceSegment_051_1782_0013, g32p_row02_traceSegment_051_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1809 13 14, g32p_row02_traceSegment_051_1809_0013, g32p_row02_traceSegment_051_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1782 27 27, g32p_row02_traceSegment_051_1782_0027, g32p_row02_traceSegment_051_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1728 54 54, g32p_row02_traceSegment_051_1728_0054, g32p_row02_traceSegment_051_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1836 13 14, g32p_row02_traceSegment_051_1836_0013, g32p_row02_traceSegment_051_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1863 13 14, g32p_row02_traceSegment_051_1863_0013, g32p_row02_traceSegment_051_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1836 27 27, g32p_row02_traceSegment_051_1836_0027, g32p_row02_traceSegment_051_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1890 13 14, g32p_row02_traceSegment_051_1890_0013, g32p_row02_traceSegment_051_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1917 13 14, g32p_row02_traceSegment_051_1917_0013, g32p_row02_traceSegment_051_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1890 27 27, g32p_row02_traceSegment_051_1890_0027, g32p_row02_traceSegment_051_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1836 54 54, g32p_row02_traceSegment_051_1836_0054, g32p_row02_traceSegment_051_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1728 108 108, g32p_row02_traceSegment_051_1728_0108, g32p_row02_traceSegment_051_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1944 13 14, g32p_row02_traceSegment_051_1944_0013, g32p_row02_traceSegment_051_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1971 13 14, g32p_row02_traceSegment_051_1971_0013, g32p_row02_traceSegment_051_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1944 27 27, g32p_row02_traceSegment_051_1944_0027, g32p_row02_traceSegment_051_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1998 13 14, g32p_row02_traceSegment_051_1998_0013, g32p_row02_traceSegment_051_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2025 13 14, g32p_row02_traceSegment_051_2025_0013, g32p_row02_traceSegment_051_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1998 27 27, g32p_row02_traceSegment_051_1998_0027, g32p_row02_traceSegment_051_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1944 54 54, g32p_row02_traceSegment_051_1944_0054, g32p_row02_traceSegment_051_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2052 13 14, g32p_row02_traceSegment_051_2052_0013, g32p_row02_traceSegment_051_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2079 13 14, g32p_row02_traceSegment_051_2079_0013, g32p_row02_traceSegment_051_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2052 27 27, g32p_row02_traceSegment_051_2052_0027, g32p_row02_traceSegment_051_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2106 13 14, g32p_row02_traceSegment_051_2106_0013, g32p_row02_traceSegment_051_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2133 13 14, g32p_row02_traceSegment_051_2133_0013, g32p_row02_traceSegment_051_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2106 27 27, g32p_row02_traceSegment_051_2106_0027, g32p_row02_traceSegment_051_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2052 54 54, g32p_row02_traceSegment_051_2052_0054, g32p_row02_traceSegment_051_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1944 108 108, g32p_row02_traceSegment_051_1944_0108, g32p_row02_traceSegment_051_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1728 216 216, g32p_row02_traceSegment_051_1728_0216, g32p_row02_traceSegment_051_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2160 13 14, g32p_row02_traceSegment_051_2160_0013, g32p_row02_traceSegment_051_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2187 13 14, g32p_row02_traceSegment_051_2187_0013, g32p_row02_traceSegment_051_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2160 27 27, g32p_row02_traceSegment_051_2160_0027, g32p_row02_traceSegment_051_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2214 13 14, g32p_row02_traceSegment_051_2214_0013, g32p_row02_traceSegment_051_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2241 13 14, g32p_row02_traceSegment_051_2241_0013, g32p_row02_traceSegment_051_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2214 27 27, g32p_row02_traceSegment_051_2214_0027, g32p_row02_traceSegment_051_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2160 54 54, g32p_row02_traceSegment_051_2160_0054, g32p_row02_traceSegment_051_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2268 13 14, g32p_row02_traceSegment_051_2268_0013, g32p_row02_traceSegment_051_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2295 13 14, g32p_row02_traceSegment_051_2295_0013, g32p_row02_traceSegment_051_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2268 27 27, g32p_row02_traceSegment_051_2268_0027, g32p_row02_traceSegment_051_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2322 13 14, g32p_row02_traceSegment_051_2322_0013, g32p_row02_traceSegment_051_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2349 13 14, g32p_row02_traceSegment_051_2349_0013, g32p_row02_traceSegment_051_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2322 27 27, g32p_row02_traceSegment_051_2322_0027, g32p_row02_traceSegment_051_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2268 54 54, g32p_row02_traceSegment_051_2268_0054, g32p_row02_traceSegment_051_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2160 108 108, g32p_row02_traceSegment_051_2160_0108, g32p_row02_traceSegment_051_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2376 13 14, g32p_row02_traceSegment_051_2376_0013, g32p_row02_traceSegment_051_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2403 13 14, g32p_row02_traceSegment_051_2403_0013, g32p_row02_traceSegment_051_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2376 27 27, g32p_row02_traceSegment_051_2376_0027, g32p_row02_traceSegment_051_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2430 13 14, g32p_row02_traceSegment_051_2430_0013, g32p_row02_traceSegment_051_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2457 13 14, g32p_row02_traceSegment_051_2457_0013, g32p_row02_traceSegment_051_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2430 27 27, g32p_row02_traceSegment_051_2430_0027, g32p_row02_traceSegment_051_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2376 54 54, g32p_row02_traceSegment_051_2376_0054, g32p_row02_traceSegment_051_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2484 13 14, g32p_row02_traceSegment_051_2484_0013, g32p_row02_traceSegment_051_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2511 13 14, g32p_row02_traceSegment_051_2511_0013, g32p_row02_traceSegment_051_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2484 27 27, g32p_row02_traceSegment_051_2484_0027, g32p_row02_traceSegment_051_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2538 13 14, g32p_row02_traceSegment_051_2538_0013, g32p_row02_traceSegment_051_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2565 13 14, g32p_row02_traceSegment_051_2565_0013, g32p_row02_traceSegment_051_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2538 27 27, g32p_row02_traceSegment_051_2538_0027, g32p_row02_traceSegment_051_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2484 54 54, g32p_row02_traceSegment_051_2484_0054, g32p_row02_traceSegment_051_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2376 108 108, g32p_row02_traceSegment_051_2376_0108, g32p_row02_traceSegment_051_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2160 216 216, g32p_row02_traceSegment_051_2160_0216, g32p_row02_traceSegment_051_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1728 432 432, g32p_row02_traceSegment_051_1728_0432, g32p_row02_traceSegment_051_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2605 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2592 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2592 13 14, g32p_row02_traceSegment_051_2592_0013, g32p_row02_traceSegment_051_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2619 13 14, g32p_row02_traceSegment_051_2619_0013, g32p_row02_traceSegment_051_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2592 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2592 27 27, g32p_row02_traceSegment_051_2592_0027, g32p_row02_traceSegment_051_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2646 13 14, g32p_row02_traceSegment_051_2646_0013, g32p_row02_traceSegment_051_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2673 13 14, g32p_row02_traceSegment_051_2673_0013, g32p_row02_traceSegment_051_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2646 27 27, g32p_row02_traceSegment_051_2646_0027, g32p_row02_traceSegment_051_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2592 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2592 54 54, g32p_row02_traceSegment_051_2592_0054, g32p_row02_traceSegment_051_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2700 13 14, g32p_row02_traceSegment_051_2700_0013, g32p_row02_traceSegment_051_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2727 13 14, g32p_row02_traceSegment_051_2727_0013, g32p_row02_traceSegment_051_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2700 27 27, g32p_row02_traceSegment_051_2700_0027, g32p_row02_traceSegment_051_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2754 13 14, g32p_row02_traceSegment_051_2754_0013, g32p_row02_traceSegment_051_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2781 13 14, g32p_row02_traceSegment_051_2781_0013, g32p_row02_traceSegment_051_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2754 27 27, g32p_row02_traceSegment_051_2754_0027, g32p_row02_traceSegment_051_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2700 54 54, g32p_row02_traceSegment_051_2700_0054, g32p_row02_traceSegment_051_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 2592 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2592 108 108, g32p_row02_traceSegment_051_2592_0108, g32p_row02_traceSegment_051_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2808 13 14, g32p_row02_traceSegment_051_2808_0013, g32p_row02_traceSegment_051_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2848 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2835 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2835 13 14, g32p_row02_traceSegment_051_2835_0013, g32p_row02_traceSegment_051_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2808 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2808 27 27, g32p_row02_traceSegment_051_2808_0027, g32p_row02_traceSegment_051_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2875 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2862 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2862 13 14, g32p_row02_traceSegment_051_2862_0013, g32p_row02_traceSegment_051_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2889 13 14, g32p_row02_traceSegment_051_2889_0013, g32p_row02_traceSegment_051_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2862 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2862 27 27, g32p_row02_traceSegment_051_2862_0027, g32p_row02_traceSegment_051_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2808 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2808 54 54, g32p_row02_traceSegment_051_2808_0054, g32p_row02_traceSegment_051_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2916 13 14, g32p_row02_traceSegment_051_2916_0013, g32p_row02_traceSegment_051_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2943 13 14, g32p_row02_traceSegment_051_2943_0013, g32p_row02_traceSegment_051_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2916 27 27, g32p_row02_traceSegment_051_2916_0027, g32p_row02_traceSegment_051_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2970 13 14, g32p_row02_traceSegment_051_2970_0013, g32p_row02_traceSegment_051_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2997 13 14, g32p_row02_traceSegment_051_2997_0013, g32p_row02_traceSegment_051_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2970 27 27, g32p_row02_traceSegment_051_2970_0027, g32p_row02_traceSegment_051_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2916 54 54, g32p_row02_traceSegment_051_2916_0054, g32p_row02_traceSegment_051_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 2808 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2808 108 108, g32p_row02_traceSegment_051_2808_0108, g32p_row02_traceSegment_051_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 2592 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2592 216 216, g32p_row02_traceSegment_051_2592_0216, g32p_row02_traceSegment_051_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3024 13 14, g32p_row02_traceSegment_051_3024_0013, g32p_row02_traceSegment_051_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3051 13 14, g32p_row02_traceSegment_051_3051_0013, g32p_row02_traceSegment_051_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3024 27 27, g32p_row02_traceSegment_051_3024_0027, g32p_row02_traceSegment_051_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3078 13 14, g32p_row02_traceSegment_051_3078_0013, g32p_row02_traceSegment_051_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3105 13 14, g32p_row02_traceSegment_051_3105_0013, g32p_row02_traceSegment_051_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3078 27 27, g32p_row02_traceSegment_051_3078_0027, g32p_row02_traceSegment_051_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3024 54 54, g32p_row02_traceSegment_051_3024_0054, g32p_row02_traceSegment_051_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3132 13 14, g32p_row02_traceSegment_051_3132_0013, g32p_row02_traceSegment_051_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3159 13 14, g32p_row02_traceSegment_051_3159_0013, g32p_row02_traceSegment_051_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3132 27 27, g32p_row02_traceSegment_051_3132_0027, g32p_row02_traceSegment_051_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3199 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3186 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3186 13 14, g32p_row02_traceSegment_051_3186_0013, g32p_row02_traceSegment_051_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3213 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3213 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3213 13 14, g32p_row02_traceSegment_051_3213_0013, g32p_row02_traceSegment_051_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3186 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3186 27 27, g32p_row02_traceSegment_051_3186_0027, g32p_row02_traceSegment_051_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 3132 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3132 54 54, g32p_row02_traceSegment_051_3132_0054, g32p_row02_traceSegment_051_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 3024 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3024 108 108, g32p_row02_traceSegment_051_3024_0108, g32p_row02_traceSegment_051_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3240 13 14, g32p_row02_traceSegment_051_3240_0013, g32p_row02_traceSegment_051_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3280 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3267 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3267 13 14, g32p_row02_traceSegment_051_3267_0013, g32p_row02_traceSegment_051_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3240 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3240 27 27, g32p_row02_traceSegment_051_3240_0027, g32p_row02_traceSegment_051_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3294 13 14, g32p_row02_traceSegment_051_3294_0013, g32p_row02_traceSegment_051_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3321 13 14, g32p_row02_traceSegment_051_3321_0013, g32p_row02_traceSegment_051_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3294 27 27, g32p_row02_traceSegment_051_3294_0027, g32p_row02_traceSegment_051_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 3240 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3240 54 54, g32p_row02_traceSegment_051_3240_0054, g32p_row02_traceSegment_051_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3348 13 14, g32p_row02_traceSegment_051_3348_0013, g32p_row02_traceSegment_051_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3375 13 14, g32p_row02_traceSegment_051_3375_0013, g32p_row02_traceSegment_051_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3348 27 27, g32p_row02_traceSegment_051_3348_0027, g32p_row02_traceSegment_051_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3402 13 14, g32p_row02_traceSegment_051_3402_0013, g32p_row02_traceSegment_051_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_051 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_051 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_051_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_051 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3429 13 14, g32p_row02_traceSegment_051_3429_0013, g32p_row02_traceSegment_051_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_051 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3402 27 27, g32p_row02_traceSegment_051_3402_0027, g32p_row02_traceSegment_051_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_051 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3348 54 54, g32p_row02_traceSegment_051_3348_0054, g32p_row02_traceSegment_051_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_051 3240 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3240 108 108, g32p_row02_traceSegment_051_3240_0108, g32p_row02_traceSegment_051_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_051_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_051 3024 432 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 3024 216 216, g32p_row02_traceSegment_051_3024_0216, g32p_row02_traceSegment_051_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_051_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_051 2592 864 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 2592 432 432, g32p_row02_traceSegment_051_2592_0432, g32p_row02_traceSegment_051_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_051_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_051 1728 1728 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 1728 864 864, g32p_row02_traceSegment_051_1728_0864, g32p_row02_traceSegment_051_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_051_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_051 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_051 0 1728 1728, g32p_row02_traceSegment_051_0000_1728, g32p_row02_traceSegment_051_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 51 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_051_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_052 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 52 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_052_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 13 14, g32p_row02_traceSegment_052_0000_0013, g32p_row02_traceSegment_052_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 27 13 14, g32p_row02_traceSegment_052_0027_0013, g32p_row02_traceSegment_052_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 27 27, g32p_row02_traceSegment_052_0000_0027, g32p_row02_traceSegment_052_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 54 13 14, g32p_row02_traceSegment_052_0054_0013, g32p_row02_traceSegment_052_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 81 13 14, g32p_row02_traceSegment_052_0081_0013, g32p_row02_traceSegment_052_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 54 27 27, g32p_row02_traceSegment_052_0054_0027, g32p_row02_traceSegment_052_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 54 54, g32p_row02_traceSegment_052_0000_0054, g32p_row02_traceSegment_052_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 108 13 14, g32p_row02_traceSegment_052_0108_0013, g32p_row02_traceSegment_052_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 135 13 14, g32p_row02_traceSegment_052_0135_0013, g32p_row02_traceSegment_052_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 108 27 27, g32p_row02_traceSegment_052_0108_0027, g32p_row02_traceSegment_052_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 162 13 14, g32p_row02_traceSegment_052_0162_0013, g32p_row02_traceSegment_052_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 189 13 14, g32p_row02_traceSegment_052_0189_0013, g32p_row02_traceSegment_052_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 162 27 27, g32p_row02_traceSegment_052_0162_0027, g32p_row02_traceSegment_052_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 108 54 54, g32p_row02_traceSegment_052_0108_0054, g32p_row02_traceSegment_052_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 108 108, g32p_row02_traceSegment_052_0000_0108, g32p_row02_traceSegment_052_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 216 13 14, g32p_row02_traceSegment_052_0216_0013, g32p_row02_traceSegment_052_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 243 13 14, g32p_row02_traceSegment_052_0243_0013, g32p_row02_traceSegment_052_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 216 27 27, g32p_row02_traceSegment_052_0216_0027, g32p_row02_traceSegment_052_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 270 13 14, g32p_row02_traceSegment_052_0270_0013, g32p_row02_traceSegment_052_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 297 13 14, g32p_row02_traceSegment_052_0297_0013, g32p_row02_traceSegment_052_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 270 27 27, g32p_row02_traceSegment_052_0270_0027, g32p_row02_traceSegment_052_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 216 54 54, g32p_row02_traceSegment_052_0216_0054, g32p_row02_traceSegment_052_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 324 13 14, g32p_row02_traceSegment_052_0324_0013, g32p_row02_traceSegment_052_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 351 13 14, g32p_row02_traceSegment_052_0351_0013, g32p_row02_traceSegment_052_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 324 27 27, g32p_row02_traceSegment_052_0324_0027, g32p_row02_traceSegment_052_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 378 13 14, g32p_row02_traceSegment_052_0378_0013, g32p_row02_traceSegment_052_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 405 13 14, g32p_row02_traceSegment_052_0405_0013, g32p_row02_traceSegment_052_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 378 27 27, g32p_row02_traceSegment_052_0378_0027, g32p_row02_traceSegment_052_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 324 54 54, g32p_row02_traceSegment_052_0324_0054, g32p_row02_traceSegment_052_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 216 108 108, g32p_row02_traceSegment_052_0216_0108, g32p_row02_traceSegment_052_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 216 216, g32p_row02_traceSegment_052_0000_0216, g32p_row02_traceSegment_052_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 432 13 14, g32p_row02_traceSegment_052_0432_0013, g32p_row02_traceSegment_052_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 459 13 14, g32p_row02_traceSegment_052_0459_0013, g32p_row02_traceSegment_052_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 432 27 27, g32p_row02_traceSegment_052_0432_0027, g32p_row02_traceSegment_052_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 486 13 14, g32p_row02_traceSegment_052_0486_0013, g32p_row02_traceSegment_052_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 513 13 14, g32p_row02_traceSegment_052_0513_0013, g32p_row02_traceSegment_052_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 486 27 27, g32p_row02_traceSegment_052_0486_0027, g32p_row02_traceSegment_052_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 432 54 54, g32p_row02_traceSegment_052_0432_0054, g32p_row02_traceSegment_052_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 540 13 14, g32p_row02_traceSegment_052_0540_0013, g32p_row02_traceSegment_052_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 567 13 14, g32p_row02_traceSegment_052_0567_0013, g32p_row02_traceSegment_052_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 540 27 27, g32p_row02_traceSegment_052_0540_0027, g32p_row02_traceSegment_052_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 594 13 14, g32p_row02_traceSegment_052_0594_0013, g32p_row02_traceSegment_052_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 621 13 14, g32p_row02_traceSegment_052_0621_0013, g32p_row02_traceSegment_052_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 594 27 27, g32p_row02_traceSegment_052_0594_0027, g32p_row02_traceSegment_052_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 540 54 54, g32p_row02_traceSegment_052_0540_0054, g32p_row02_traceSegment_052_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 432 108 108, g32p_row02_traceSegment_052_0432_0108, g32p_row02_traceSegment_052_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 648 13 14, g32p_row02_traceSegment_052_0648_0013, g32p_row02_traceSegment_052_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 675 13 14, g32p_row02_traceSegment_052_0675_0013, g32p_row02_traceSegment_052_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 648 27 27, g32p_row02_traceSegment_052_0648_0027, g32p_row02_traceSegment_052_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 702 13 14, g32p_row02_traceSegment_052_0702_0013, g32p_row02_traceSegment_052_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 729 13 14, g32p_row02_traceSegment_052_0729_0013, g32p_row02_traceSegment_052_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 702 27 27, g32p_row02_traceSegment_052_0702_0027, g32p_row02_traceSegment_052_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 648 54 54, g32p_row02_traceSegment_052_0648_0054, g32p_row02_traceSegment_052_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 756 13 14, g32p_row02_traceSegment_052_0756_0013, g32p_row02_traceSegment_052_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 783 13 14, g32p_row02_traceSegment_052_0783_0013, g32p_row02_traceSegment_052_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 756 27 27, g32p_row02_traceSegment_052_0756_0027, g32p_row02_traceSegment_052_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 810 13 14, g32p_row02_traceSegment_052_0810_0013, g32p_row02_traceSegment_052_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 837 13 14, g32p_row02_traceSegment_052_0837_0013, g32p_row02_traceSegment_052_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 810 27 27, g32p_row02_traceSegment_052_0810_0027, g32p_row02_traceSegment_052_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 756 54 54, g32p_row02_traceSegment_052_0756_0054, g32p_row02_traceSegment_052_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 648 108 108, g32p_row02_traceSegment_052_0648_0108, g32p_row02_traceSegment_052_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 432 216 216, g32p_row02_traceSegment_052_0432_0216, g32p_row02_traceSegment_052_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_052 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 432 432, g32p_row02_traceSegment_052_0000_0432, g32p_row02_traceSegment_052_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 864 13 14, g32p_row02_traceSegment_052_0864_0013, g32p_row02_traceSegment_052_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 891 13 14, g32p_row02_traceSegment_052_0891_0013, g32p_row02_traceSegment_052_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 864 27 27, g32p_row02_traceSegment_052_0864_0027, g32p_row02_traceSegment_052_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 918 13 14, g32p_row02_traceSegment_052_0918_0013, g32p_row02_traceSegment_052_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 945 13 14, g32p_row02_traceSegment_052_0945_0013, g32p_row02_traceSegment_052_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 918 27 27, g32p_row02_traceSegment_052_0918_0027, g32p_row02_traceSegment_052_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 864 54 54, g32p_row02_traceSegment_052_0864_0054, g32p_row02_traceSegment_052_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 972 13 14, g32p_row02_traceSegment_052_0972_0013, g32p_row02_traceSegment_052_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 999 13 14, g32p_row02_traceSegment_052_0999_0013, g32p_row02_traceSegment_052_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 972 27 27, g32p_row02_traceSegment_052_0972_0027, g32p_row02_traceSegment_052_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1026 13 14, g32p_row02_traceSegment_052_1026_0013, g32p_row02_traceSegment_052_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1053 13 14, g32p_row02_traceSegment_052_1053_0013, g32p_row02_traceSegment_052_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1026 27 27, g32p_row02_traceSegment_052_1026_0027, g32p_row02_traceSegment_052_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 972 54 54, g32p_row02_traceSegment_052_0972_0054, g32p_row02_traceSegment_052_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 864 108 108, g32p_row02_traceSegment_052_0864_0108, g32p_row02_traceSegment_052_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1080 13 14, g32p_row02_traceSegment_052_1080_0013, g32p_row02_traceSegment_052_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1107 13 14, g32p_row02_traceSegment_052_1107_0013, g32p_row02_traceSegment_052_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1080 27 27, g32p_row02_traceSegment_052_1080_0027, g32p_row02_traceSegment_052_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1134 13 14, g32p_row02_traceSegment_052_1134_0013, g32p_row02_traceSegment_052_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1161 13 14, g32p_row02_traceSegment_052_1161_0013, g32p_row02_traceSegment_052_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1134 27 27, g32p_row02_traceSegment_052_1134_0027, g32p_row02_traceSegment_052_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1080 54 54, g32p_row02_traceSegment_052_1080_0054, g32p_row02_traceSegment_052_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1188 13 14, g32p_row02_traceSegment_052_1188_0013, g32p_row02_traceSegment_052_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1215 13 14, g32p_row02_traceSegment_052_1215_0013, g32p_row02_traceSegment_052_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1188 27 27, g32p_row02_traceSegment_052_1188_0027, g32p_row02_traceSegment_052_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1242 13 14, g32p_row02_traceSegment_052_1242_0013, g32p_row02_traceSegment_052_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1269 13 14, g32p_row02_traceSegment_052_1269_0013, g32p_row02_traceSegment_052_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1242 27 27, g32p_row02_traceSegment_052_1242_0027, g32p_row02_traceSegment_052_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1188 54 54, g32p_row02_traceSegment_052_1188_0054, g32p_row02_traceSegment_052_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1080 108 108, g32p_row02_traceSegment_052_1080_0108, g32p_row02_traceSegment_052_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 864 216 216, g32p_row02_traceSegment_052_0864_0216, g32p_row02_traceSegment_052_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1296 13 14, g32p_row02_traceSegment_052_1296_0013, g32p_row02_traceSegment_052_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1323 13 14, g32p_row02_traceSegment_052_1323_0013, g32p_row02_traceSegment_052_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1296 27 27, g32p_row02_traceSegment_052_1296_0027, g32p_row02_traceSegment_052_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1350 13 14, g32p_row02_traceSegment_052_1350_0013, g32p_row02_traceSegment_052_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1377 13 14, g32p_row02_traceSegment_052_1377_0013, g32p_row02_traceSegment_052_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1350 27 27, g32p_row02_traceSegment_052_1350_0027, g32p_row02_traceSegment_052_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1296 54 54, g32p_row02_traceSegment_052_1296_0054, g32p_row02_traceSegment_052_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1404 13 14, g32p_row02_traceSegment_052_1404_0013, g32p_row02_traceSegment_052_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1431 13 14, g32p_row02_traceSegment_052_1431_0013, g32p_row02_traceSegment_052_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1404 27 27, g32p_row02_traceSegment_052_1404_0027, g32p_row02_traceSegment_052_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1458 13 14, g32p_row02_traceSegment_052_1458_0013, g32p_row02_traceSegment_052_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1485 13 14, g32p_row02_traceSegment_052_1485_0013, g32p_row02_traceSegment_052_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1458 27 27, g32p_row02_traceSegment_052_1458_0027, g32p_row02_traceSegment_052_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1404 54 54, g32p_row02_traceSegment_052_1404_0054, g32p_row02_traceSegment_052_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1296 108 108, g32p_row02_traceSegment_052_1296_0108, g32p_row02_traceSegment_052_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1512 13 14, g32p_row02_traceSegment_052_1512_0013, g32p_row02_traceSegment_052_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1539 13 14, g32p_row02_traceSegment_052_1539_0013, g32p_row02_traceSegment_052_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1512 27 27, g32p_row02_traceSegment_052_1512_0027, g32p_row02_traceSegment_052_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1566 13 14, g32p_row02_traceSegment_052_1566_0013, g32p_row02_traceSegment_052_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1593 13 14, g32p_row02_traceSegment_052_1593_0013, g32p_row02_traceSegment_052_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1566 27 27, g32p_row02_traceSegment_052_1566_0027, g32p_row02_traceSegment_052_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1512 54 54, g32p_row02_traceSegment_052_1512_0054, g32p_row02_traceSegment_052_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1620 13 14, g32p_row02_traceSegment_052_1620_0013, g32p_row02_traceSegment_052_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1647 13 14, g32p_row02_traceSegment_052_1647_0013, g32p_row02_traceSegment_052_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1620 27 27, g32p_row02_traceSegment_052_1620_0027, g32p_row02_traceSegment_052_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1674 13 14, g32p_row02_traceSegment_052_1674_0013, g32p_row02_traceSegment_052_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1701 13 14, g32p_row02_traceSegment_052_1701_0013, g32p_row02_traceSegment_052_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1674 27 27, g32p_row02_traceSegment_052_1674_0027, g32p_row02_traceSegment_052_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1620 54 54, g32p_row02_traceSegment_052_1620_0054, g32p_row02_traceSegment_052_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1512 108 108, g32p_row02_traceSegment_052_1512_0108, g32p_row02_traceSegment_052_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1296 216 216, g32p_row02_traceSegment_052_1296_0216, g32p_row02_traceSegment_052_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_052 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 864 432 432, g32p_row02_traceSegment_052_0864_0432, g32p_row02_traceSegment_052_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_052 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 864 864, g32p_row02_traceSegment_052_0000_0864, g32p_row02_traceSegment_052_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1728 13 14, g32p_row02_traceSegment_052_1728_0013, g32p_row02_traceSegment_052_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1755 13 14, g32p_row02_traceSegment_052_1755_0013, g32p_row02_traceSegment_052_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1728 27 27, g32p_row02_traceSegment_052_1728_0027, g32p_row02_traceSegment_052_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1782 13 14, g32p_row02_traceSegment_052_1782_0013, g32p_row02_traceSegment_052_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1809 13 14, g32p_row02_traceSegment_052_1809_0013, g32p_row02_traceSegment_052_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1782 27 27, g32p_row02_traceSegment_052_1782_0027, g32p_row02_traceSegment_052_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1728 54 54, g32p_row02_traceSegment_052_1728_0054, g32p_row02_traceSegment_052_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1836 13 14, g32p_row02_traceSegment_052_1836_0013, g32p_row02_traceSegment_052_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1863 13 14, g32p_row02_traceSegment_052_1863_0013, g32p_row02_traceSegment_052_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1836 27 27, g32p_row02_traceSegment_052_1836_0027, g32p_row02_traceSegment_052_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1890 13 14, g32p_row02_traceSegment_052_1890_0013, g32p_row02_traceSegment_052_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1917 13 14, g32p_row02_traceSegment_052_1917_0013, g32p_row02_traceSegment_052_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1890 27 27, g32p_row02_traceSegment_052_1890_0027, g32p_row02_traceSegment_052_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1836 54 54, g32p_row02_traceSegment_052_1836_0054, g32p_row02_traceSegment_052_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1728 108 108, g32p_row02_traceSegment_052_1728_0108, g32p_row02_traceSegment_052_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1944 13 14, g32p_row02_traceSegment_052_1944_0013, g32p_row02_traceSegment_052_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1971 13 14, g32p_row02_traceSegment_052_1971_0013, g32p_row02_traceSegment_052_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1944 27 27, g32p_row02_traceSegment_052_1944_0027, g32p_row02_traceSegment_052_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1998 13 14, g32p_row02_traceSegment_052_1998_0013, g32p_row02_traceSegment_052_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2025 13 14, g32p_row02_traceSegment_052_2025_0013, g32p_row02_traceSegment_052_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1998 27 27, g32p_row02_traceSegment_052_1998_0027, g32p_row02_traceSegment_052_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1944 54 54, g32p_row02_traceSegment_052_1944_0054, g32p_row02_traceSegment_052_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2052 13 14, g32p_row02_traceSegment_052_2052_0013, g32p_row02_traceSegment_052_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2079 13 14, g32p_row02_traceSegment_052_2079_0013, g32p_row02_traceSegment_052_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2052 27 27, g32p_row02_traceSegment_052_2052_0027, g32p_row02_traceSegment_052_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2106 13 14, g32p_row02_traceSegment_052_2106_0013, g32p_row02_traceSegment_052_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2133 13 14, g32p_row02_traceSegment_052_2133_0013, g32p_row02_traceSegment_052_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2106 27 27, g32p_row02_traceSegment_052_2106_0027, g32p_row02_traceSegment_052_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2052 54 54, g32p_row02_traceSegment_052_2052_0054, g32p_row02_traceSegment_052_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1944 108 108, g32p_row02_traceSegment_052_1944_0108, g32p_row02_traceSegment_052_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1728 216 216, g32p_row02_traceSegment_052_1728_0216, g32p_row02_traceSegment_052_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2160 13 14, g32p_row02_traceSegment_052_2160_0013, g32p_row02_traceSegment_052_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2187 13 14, g32p_row02_traceSegment_052_2187_0013, g32p_row02_traceSegment_052_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2160 27 27, g32p_row02_traceSegment_052_2160_0027, g32p_row02_traceSegment_052_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2214 13 14, g32p_row02_traceSegment_052_2214_0013, g32p_row02_traceSegment_052_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2241 13 14, g32p_row02_traceSegment_052_2241_0013, g32p_row02_traceSegment_052_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2214 27 27, g32p_row02_traceSegment_052_2214_0027, g32p_row02_traceSegment_052_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2160 54 54, g32p_row02_traceSegment_052_2160_0054, g32p_row02_traceSegment_052_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2268 13 14, g32p_row02_traceSegment_052_2268_0013, g32p_row02_traceSegment_052_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2295 13 14, g32p_row02_traceSegment_052_2295_0013, g32p_row02_traceSegment_052_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2268 27 27, g32p_row02_traceSegment_052_2268_0027, g32p_row02_traceSegment_052_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2322 13 14, g32p_row02_traceSegment_052_2322_0013, g32p_row02_traceSegment_052_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2349 13 14, g32p_row02_traceSegment_052_2349_0013, g32p_row02_traceSegment_052_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2322 27 27, g32p_row02_traceSegment_052_2322_0027, g32p_row02_traceSegment_052_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2268 54 54, g32p_row02_traceSegment_052_2268_0054, g32p_row02_traceSegment_052_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2160 108 108, g32p_row02_traceSegment_052_2160_0108, g32p_row02_traceSegment_052_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2376 13 14, g32p_row02_traceSegment_052_2376_0013, g32p_row02_traceSegment_052_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2403 13 14, g32p_row02_traceSegment_052_2403_0013, g32p_row02_traceSegment_052_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2376 27 27, g32p_row02_traceSegment_052_2376_0027, g32p_row02_traceSegment_052_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2430 13 14, g32p_row02_traceSegment_052_2430_0013, g32p_row02_traceSegment_052_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2457 13 14, g32p_row02_traceSegment_052_2457_0013, g32p_row02_traceSegment_052_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2430 27 27, g32p_row02_traceSegment_052_2430_0027, g32p_row02_traceSegment_052_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2376 54 54, g32p_row02_traceSegment_052_2376_0054, g32p_row02_traceSegment_052_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2484 13 14, g32p_row02_traceSegment_052_2484_0013, g32p_row02_traceSegment_052_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2511 13 14, g32p_row02_traceSegment_052_2511_0013, g32p_row02_traceSegment_052_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2484 27 27, g32p_row02_traceSegment_052_2484_0027, g32p_row02_traceSegment_052_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2538 13 14, g32p_row02_traceSegment_052_2538_0013, g32p_row02_traceSegment_052_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2565 13 14, g32p_row02_traceSegment_052_2565_0013, g32p_row02_traceSegment_052_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2538 27 27, g32p_row02_traceSegment_052_2538_0027, g32p_row02_traceSegment_052_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2484 54 54, g32p_row02_traceSegment_052_2484_0054, g32p_row02_traceSegment_052_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2376 108 108, g32p_row02_traceSegment_052_2376_0108, g32p_row02_traceSegment_052_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2160 216 216, g32p_row02_traceSegment_052_2160_0216, g32p_row02_traceSegment_052_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1728 432 432, g32p_row02_traceSegment_052_1728_0432, g32p_row02_traceSegment_052_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2592 13 14, g32p_row02_traceSegment_052_2592_0013, g32p_row02_traceSegment_052_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2619 13 14, g32p_row02_traceSegment_052_2619_0013, g32p_row02_traceSegment_052_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2592 27 27, g32p_row02_traceSegment_052_2592_0027, g32p_row02_traceSegment_052_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2646 13 14, g32p_row02_traceSegment_052_2646_0013, g32p_row02_traceSegment_052_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2673 13 14, g32p_row02_traceSegment_052_2673_0013, g32p_row02_traceSegment_052_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2646 27 27, g32p_row02_traceSegment_052_2646_0027, g32p_row02_traceSegment_052_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2592 54 54, g32p_row02_traceSegment_052_2592_0054, g32p_row02_traceSegment_052_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2713 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2700 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2700 13 14, g32p_row02_traceSegment_052_2700_0013, g32p_row02_traceSegment_052_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2727 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2740 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2727 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2727 13 14, g32p_row02_traceSegment_052_2727_0013, g32p_row02_traceSegment_052_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2700 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2700 27 27, g32p_row02_traceSegment_052_2700_0027, g32p_row02_traceSegment_052_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2754 13 14, g32p_row02_traceSegment_052_2754_0013, g32p_row02_traceSegment_052_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2781 13 14, g32p_row02_traceSegment_052_2781_0013, g32p_row02_traceSegment_052_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2754 27 27, g32p_row02_traceSegment_052_2754_0027, g32p_row02_traceSegment_052_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2700 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2700 54 54, g32p_row02_traceSegment_052_2700_0054, g32p_row02_traceSegment_052_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 2592 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2592 108 108, g32p_row02_traceSegment_052_2592_0108, g32p_row02_traceSegment_052_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2808 13 14, g32p_row02_traceSegment_052_2808_0013, g32p_row02_traceSegment_052_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2835 13 14, g32p_row02_traceSegment_052_2835_0013, g32p_row02_traceSegment_052_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2808 27 27, g32p_row02_traceSegment_052_2808_0027, g32p_row02_traceSegment_052_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2862 13 14, g32p_row02_traceSegment_052_2862_0013, g32p_row02_traceSegment_052_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2889 13 14, g32p_row02_traceSegment_052_2889_0013, g32p_row02_traceSegment_052_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2862 27 27, g32p_row02_traceSegment_052_2862_0027, g32p_row02_traceSegment_052_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2808 54 54, g32p_row02_traceSegment_052_2808_0054, g32p_row02_traceSegment_052_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2916 13 14, g32p_row02_traceSegment_052_2916_0013, g32p_row02_traceSegment_052_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2943 13 14, g32p_row02_traceSegment_052_2943_0013, g32p_row02_traceSegment_052_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2916 27 27, g32p_row02_traceSegment_052_2916_0027, g32p_row02_traceSegment_052_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2970 13 14, g32p_row02_traceSegment_052_2970_0013, g32p_row02_traceSegment_052_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3010 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 2997 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2997 13 14, g32p_row02_traceSegment_052_2997_0013, g32p_row02_traceSegment_052_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 2970 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2970 27 27, g32p_row02_traceSegment_052_2970_0027, g32p_row02_traceSegment_052_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 2916 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2916 54 54, g32p_row02_traceSegment_052_2916_0054, g32p_row02_traceSegment_052_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 2808 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2808 108 108, g32p_row02_traceSegment_052_2808_0108, g32p_row02_traceSegment_052_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 2592 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2592 216 216, g32p_row02_traceSegment_052_2592_0216, g32p_row02_traceSegment_052_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3024 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3037 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3024 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3024 13 14, g32p_row02_traceSegment_052_3024_0013, g32p_row02_traceSegment_052_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3051 13 14, g32p_row02_traceSegment_052_3051_0013, g32p_row02_traceSegment_052_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3024 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3024 27 27, g32p_row02_traceSegment_052_3024_0027, g32p_row02_traceSegment_052_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3091 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3078 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3078 13 14, g32p_row02_traceSegment_052_3078_0013, g32p_row02_traceSegment_052_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3118 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3105 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3105 13 14, g32p_row02_traceSegment_052_3105_0013, g32p_row02_traceSegment_052_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3078 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3078 27 27, g32p_row02_traceSegment_052_3078_0027, g32p_row02_traceSegment_052_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 3024 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3024 54 54, g32p_row02_traceSegment_052_3024_0054, g32p_row02_traceSegment_052_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3132 13 14, g32p_row02_traceSegment_052_3132_0013, g32p_row02_traceSegment_052_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3159 13 14, g32p_row02_traceSegment_052_3159_0013, g32p_row02_traceSegment_052_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3132 27 27, g32p_row02_traceSegment_052_3132_0027, g32p_row02_traceSegment_052_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3186 13 14, g32p_row02_traceSegment_052_3186_0013, g32p_row02_traceSegment_052_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3213 13 14, g32p_row02_traceSegment_052_3213_0013, g32p_row02_traceSegment_052_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3186 27 27, g32p_row02_traceSegment_052_3186_0027, g32p_row02_traceSegment_052_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3132 54 54, g32p_row02_traceSegment_052_3132_0054, g32p_row02_traceSegment_052_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 3024 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3024 108 108, g32p_row02_traceSegment_052_3024_0108, g32p_row02_traceSegment_052_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3240 13 14, g32p_row02_traceSegment_052_3240_0013, g32p_row02_traceSegment_052_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3267 13 14, g32p_row02_traceSegment_052_3267_0013, g32p_row02_traceSegment_052_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3240 27 27, g32p_row02_traceSegment_052_3240_0027, g32p_row02_traceSegment_052_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3294 13 14, g32p_row02_traceSegment_052_3294_0013, g32p_row02_traceSegment_052_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3321 13 14, g32p_row02_traceSegment_052_3321_0013, g32p_row02_traceSegment_052_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3294 27 27, g32p_row02_traceSegment_052_3294_0027, g32p_row02_traceSegment_052_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3240 54 54, g32p_row02_traceSegment_052_3240_0054, g32p_row02_traceSegment_052_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3348 13 14, g32p_row02_traceSegment_052_3348_0013, g32p_row02_traceSegment_052_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3375 13 14, g32p_row02_traceSegment_052_3375_0013, g32p_row02_traceSegment_052_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3348 27 27, g32p_row02_traceSegment_052_3348_0027, g32p_row02_traceSegment_052_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3402 13 14, g32p_row02_traceSegment_052_3402_0013, g32p_row02_traceSegment_052_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_052 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_052 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_052_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_052 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3429 13 14, g32p_row02_traceSegment_052_3429_0013, g32p_row02_traceSegment_052_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_052 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3402 27 27, g32p_row02_traceSegment_052_3402_0027, g32p_row02_traceSegment_052_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_052 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3348 54 54, g32p_row02_traceSegment_052_3348_0054, g32p_row02_traceSegment_052_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_052 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3240 108 108, g32p_row02_traceSegment_052_3240_0108, g32p_row02_traceSegment_052_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_052_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_052 3024 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 3024 216 216, g32p_row02_traceSegment_052_3024_0216, g32p_row02_traceSegment_052_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_052_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_052 2592 864 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 2592 432 432, g32p_row02_traceSegment_052_2592_0432, g32p_row02_traceSegment_052_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_052_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_052 1728 1728 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 1728 864 864, g32p_row02_traceSegment_052_1728_0864, g32p_row02_traceSegment_052_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_052_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_052 0 3456 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_052 0 1728 1728, g32p_row02_traceSegment_052_0000_1728, g32p_row02_traceSegment_052_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 52 = [0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_052_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_055 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 55 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_055_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 13 14, g32p_row02_traceSegment_055_0000_0013, g32p_row02_traceSegment_055_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 27 13 14, g32p_row02_traceSegment_055_0027_0013, g32p_row02_traceSegment_055_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 27 27, g32p_row02_traceSegment_055_0000_0027, g32p_row02_traceSegment_055_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 54 13 14, g32p_row02_traceSegment_055_0054_0013, g32p_row02_traceSegment_055_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 81 13 14, g32p_row02_traceSegment_055_0081_0013, g32p_row02_traceSegment_055_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 54 27 27, g32p_row02_traceSegment_055_0054_0027, g32p_row02_traceSegment_055_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 54 54, g32p_row02_traceSegment_055_0000_0054, g32p_row02_traceSegment_055_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 108 13 14, g32p_row02_traceSegment_055_0108_0013, g32p_row02_traceSegment_055_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 135 13 14, g32p_row02_traceSegment_055_0135_0013, g32p_row02_traceSegment_055_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 108 27 27, g32p_row02_traceSegment_055_0108_0027, g32p_row02_traceSegment_055_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 162 13 14, g32p_row02_traceSegment_055_0162_0013, g32p_row02_traceSegment_055_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 189 13 14, g32p_row02_traceSegment_055_0189_0013, g32p_row02_traceSegment_055_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 162 27 27, g32p_row02_traceSegment_055_0162_0027, g32p_row02_traceSegment_055_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 108 54 54, g32p_row02_traceSegment_055_0108_0054, g32p_row02_traceSegment_055_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 108 108, g32p_row02_traceSegment_055_0000_0108, g32p_row02_traceSegment_055_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 216 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 216 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 216 13 14, g32p_row02_traceSegment_055_0216_0013, g32p_row02_traceSegment_055_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 243 13 14, g32p_row02_traceSegment_055_0243_0013, g32p_row02_traceSegment_055_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 216 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 216 27 27, g32p_row02_traceSegment_055_0216_0027, g32p_row02_traceSegment_055_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 270 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 283 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 270 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 270 13 14, g32p_row02_traceSegment_055_0270_0013, g32p_row02_traceSegment_055_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 297 13 14, g32p_row02_traceSegment_055_0297_0013, g32p_row02_traceSegment_055_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 270 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 270 27 27, g32p_row02_traceSegment_055_0270_0027, g32p_row02_traceSegment_055_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 216 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 216 54 54, g32p_row02_traceSegment_055_0216_0054, g32p_row02_traceSegment_055_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 324 13 14, g32p_row02_traceSegment_055_0324_0013, g32p_row02_traceSegment_055_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 351 13 14, g32p_row02_traceSegment_055_0351_0013, g32p_row02_traceSegment_055_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 324 27 27, g32p_row02_traceSegment_055_0324_0027, g32p_row02_traceSegment_055_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 378 13 14, g32p_row02_traceSegment_055_0378_0013, g32p_row02_traceSegment_055_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 405 13 14, g32p_row02_traceSegment_055_0405_0013, g32p_row02_traceSegment_055_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 378 27 27, g32p_row02_traceSegment_055_0378_0027, g32p_row02_traceSegment_055_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 324 54 54, g32p_row02_traceSegment_055_0324_0054, g32p_row02_traceSegment_055_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 216 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 216 108 108, g32p_row02_traceSegment_055_0216_0108, g32p_row02_traceSegment_055_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 0 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 216 216, g32p_row02_traceSegment_055_0000_0216, g32p_row02_traceSegment_055_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 432 13 14, g32p_row02_traceSegment_055_0432_0013, g32p_row02_traceSegment_055_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 472 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 459 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 459 13 14, g32p_row02_traceSegment_055_0459_0013, g32p_row02_traceSegment_055_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 432 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 432 27 27, g32p_row02_traceSegment_055_0432_0027, g32p_row02_traceSegment_055_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 486 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 486 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 486 13 14, g32p_row02_traceSegment_055_0486_0013, g32p_row02_traceSegment_055_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 513 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 513 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 513 13 14, g32p_row02_traceSegment_055_0513_0013, g32p_row02_traceSegment_055_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 486 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 486 27 27, g32p_row02_traceSegment_055_0486_0027, g32p_row02_traceSegment_055_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 432 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 432 54 54, g32p_row02_traceSegment_055_0432_0054, g32p_row02_traceSegment_055_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 540 13 14, g32p_row02_traceSegment_055_0540_0013, g32p_row02_traceSegment_055_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 567 13 14, g32p_row02_traceSegment_055_0567_0013, g32p_row02_traceSegment_055_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 540 27 27, g32p_row02_traceSegment_055_0540_0027, g32p_row02_traceSegment_055_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 594 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 607 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 594 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 594 13 14, g32p_row02_traceSegment_055_0594_0013, g32p_row02_traceSegment_055_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 634 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 621 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 621 13 14, g32p_row02_traceSegment_055_0621_0013, g32p_row02_traceSegment_055_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 594 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 594 27 27, g32p_row02_traceSegment_055_0594_0027, g32p_row02_traceSegment_055_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 540 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 540 54 54, g32p_row02_traceSegment_055_0540_0054, g32p_row02_traceSegment_055_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 432 216 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 432 108 108, g32p_row02_traceSegment_055_0432_0108, g32p_row02_traceSegment_055_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 661 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 648 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 648 13 14, g32p_row02_traceSegment_055_0648_0013, g32p_row02_traceSegment_055_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 675 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 675 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 675 13 14, g32p_row02_traceSegment_055_0675_0013, g32p_row02_traceSegment_055_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 648 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 648 27 27, g32p_row02_traceSegment_055_0648_0027, g32p_row02_traceSegment_055_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 702 13 14, g32p_row02_traceSegment_055_0702_0013, g32p_row02_traceSegment_055_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 729 13 14, g32p_row02_traceSegment_055_0729_0013, g32p_row02_traceSegment_055_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 702 27 27, g32p_row02_traceSegment_055_0702_0027, g32p_row02_traceSegment_055_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 648 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 648 54 54, g32p_row02_traceSegment_055_0648_0054, g32p_row02_traceSegment_055_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 756 13 14, g32p_row02_traceSegment_055_0756_0013, g32p_row02_traceSegment_055_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 783 13 14, g32p_row02_traceSegment_055_0783_0013, g32p_row02_traceSegment_055_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 756 27 27, g32p_row02_traceSegment_055_0756_0027, g32p_row02_traceSegment_055_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 810 13 14, g32p_row02_traceSegment_055_0810_0013, g32p_row02_traceSegment_055_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 850 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 837 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 837 13 14, g32p_row02_traceSegment_055_0837_0013, g32p_row02_traceSegment_055_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 810 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 810 27 27, g32p_row02_traceSegment_055_0810_0027, g32p_row02_traceSegment_055_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 756 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 756 54 54, g32p_row02_traceSegment_055_0756_0054, g32p_row02_traceSegment_055_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 648 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 648 108 108, g32p_row02_traceSegment_055_0648_0108, g32p_row02_traceSegment_055_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 432 432 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 432 216 216, g32p_row02_traceSegment_055_0432_0216, g32p_row02_traceSegment_055_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_055 0 864 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 432 432, g32p_row02_traceSegment_055_0000_0432, g32p_row02_traceSegment_055_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 877 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 864 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 864 13 14, g32p_row02_traceSegment_055_0864_0013, g32p_row02_traceSegment_055_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 891 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 891 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 891 13 14, g32p_row02_traceSegment_055_0891_0013, g32p_row02_traceSegment_055_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 864 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 864 27 27, g32p_row02_traceSegment_055_0864_0027, g32p_row02_traceSegment_055_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 918 13 14, g32p_row02_traceSegment_055_0918_0013, g32p_row02_traceSegment_055_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 958 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 945 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 945 13 14, g32p_row02_traceSegment_055_0945_0013, g32p_row02_traceSegment_055_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 918 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 918 27 27, g32p_row02_traceSegment_055_0918_0027, g32p_row02_traceSegment_055_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 864 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 864 54 54, g32p_row02_traceSegment_055_0864_0054, g32p_row02_traceSegment_055_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 972 13 14, g32p_row02_traceSegment_055_0972_0013, g32p_row02_traceSegment_055_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 999 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 999 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 999 13 14, g32p_row02_traceSegment_055_0999_0013, g32p_row02_traceSegment_055_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 972 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 972 27 27, g32p_row02_traceSegment_055_0972_0027, g32p_row02_traceSegment_055_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1026 13 14, g32p_row02_traceSegment_055_1026_0013, g32p_row02_traceSegment_055_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1053 13 14, g32p_row02_traceSegment_055_1053_0013, g32p_row02_traceSegment_055_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1026 27 27, g32p_row02_traceSegment_055_1026_0027, g32p_row02_traceSegment_055_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 972 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 972 54 54, g32p_row02_traceSegment_055_0972_0054, g32p_row02_traceSegment_055_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 864 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 864 108 108, g32p_row02_traceSegment_055_0864_0108, g32p_row02_traceSegment_055_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1080 13 14, g32p_row02_traceSegment_055_1080_0013, g32p_row02_traceSegment_055_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1107 13 14, g32p_row02_traceSegment_055_1107_0013, g32p_row02_traceSegment_055_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1080 27 27, g32p_row02_traceSegment_055_1080_0027, g32p_row02_traceSegment_055_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1134 13 14, g32p_row02_traceSegment_055_1134_0013, g32p_row02_traceSegment_055_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1161 13 14, g32p_row02_traceSegment_055_1161_0013, g32p_row02_traceSegment_055_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1134 27 27, g32p_row02_traceSegment_055_1134_0027, g32p_row02_traceSegment_055_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1080 54 54, g32p_row02_traceSegment_055_1080_0054, g32p_row02_traceSegment_055_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1188 13 14, g32p_row02_traceSegment_055_1188_0013, g32p_row02_traceSegment_055_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1215 13 14, g32p_row02_traceSegment_055_1215_0013, g32p_row02_traceSegment_055_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1188 27 27, g32p_row02_traceSegment_055_1188_0027, g32p_row02_traceSegment_055_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1242 13 14, g32p_row02_traceSegment_055_1242_0013, g32p_row02_traceSegment_055_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1269 13 14, g32p_row02_traceSegment_055_1269_0013, g32p_row02_traceSegment_055_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1242 27 27, g32p_row02_traceSegment_055_1242_0027, g32p_row02_traceSegment_055_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1188 54 54, g32p_row02_traceSegment_055_1188_0054, g32p_row02_traceSegment_055_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1080 108 108, g32p_row02_traceSegment_055_1080_0108, g32p_row02_traceSegment_055_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 864 432 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 864 216 216, g32p_row02_traceSegment_055_0864_0216, g32p_row02_traceSegment_055_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1296 13 14, g32p_row02_traceSegment_055_1296_0013, g32p_row02_traceSegment_055_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1323 13 14, g32p_row02_traceSegment_055_1323_0013, g32p_row02_traceSegment_055_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1296 27 27, g32p_row02_traceSegment_055_1296_0027, g32p_row02_traceSegment_055_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1350 13 14, g32p_row02_traceSegment_055_1350_0013, g32p_row02_traceSegment_055_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1377 13 14, g32p_row02_traceSegment_055_1377_0013, g32p_row02_traceSegment_055_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1350 27 27, g32p_row02_traceSegment_055_1350_0027, g32p_row02_traceSegment_055_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1296 54 54, g32p_row02_traceSegment_055_1296_0054, g32p_row02_traceSegment_055_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1404 13 14, g32p_row02_traceSegment_055_1404_0013, g32p_row02_traceSegment_055_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1431 13 14, g32p_row02_traceSegment_055_1431_0013, g32p_row02_traceSegment_055_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1404 27 27, g32p_row02_traceSegment_055_1404_0027, g32p_row02_traceSegment_055_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1458 13 14, g32p_row02_traceSegment_055_1458_0013, g32p_row02_traceSegment_055_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1485 13 14, g32p_row02_traceSegment_055_1485_0013, g32p_row02_traceSegment_055_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1458 27 27, g32p_row02_traceSegment_055_1458_0027, g32p_row02_traceSegment_055_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1404 54 54, g32p_row02_traceSegment_055_1404_0054, g32p_row02_traceSegment_055_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1296 108 108, g32p_row02_traceSegment_055_1296_0108, g32p_row02_traceSegment_055_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1512 13 14, g32p_row02_traceSegment_055_1512_0013, g32p_row02_traceSegment_055_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1539 13 14, g32p_row02_traceSegment_055_1539_0013, g32p_row02_traceSegment_055_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1512 27 27, g32p_row02_traceSegment_055_1512_0027, g32p_row02_traceSegment_055_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1566 13 14, g32p_row02_traceSegment_055_1566_0013, g32p_row02_traceSegment_055_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1593 13 14, g32p_row02_traceSegment_055_1593_0013, g32p_row02_traceSegment_055_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1566 27 27, g32p_row02_traceSegment_055_1566_0027, g32p_row02_traceSegment_055_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1512 54 54, g32p_row02_traceSegment_055_1512_0054, g32p_row02_traceSegment_055_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1620 13 14, g32p_row02_traceSegment_055_1620_0013, g32p_row02_traceSegment_055_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1647 13 14, g32p_row02_traceSegment_055_1647_0013, g32p_row02_traceSegment_055_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1620 27 27, g32p_row02_traceSegment_055_1620_0027, g32p_row02_traceSegment_055_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1674 13 14, g32p_row02_traceSegment_055_1674_0013, g32p_row02_traceSegment_055_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1701 13 14, g32p_row02_traceSegment_055_1701_0013, g32p_row02_traceSegment_055_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1674 27 27, g32p_row02_traceSegment_055_1674_0027, g32p_row02_traceSegment_055_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1620 54 54, g32p_row02_traceSegment_055_1620_0054, g32p_row02_traceSegment_055_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1512 108 108, g32p_row02_traceSegment_055_1512_0108, g32p_row02_traceSegment_055_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1296 216 216, g32p_row02_traceSegment_055_1296_0216, g32p_row02_traceSegment_055_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_055 864 864 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 864 432 432, g32p_row02_traceSegment_055_0864_0432, g32p_row02_traceSegment_055_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_055 0 1728 = [0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 864 864, g32p_row02_traceSegment_055_0000_0864, g32p_row02_traceSegment_055_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1741 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1728 13 14, g32p_row02_traceSegment_055_1728_0013, g32p_row02_traceSegment_055_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1755 13 14, g32p_row02_traceSegment_055_1755_0013, g32p_row02_traceSegment_055_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1728 27 27, g32p_row02_traceSegment_055_1728_0027, g32p_row02_traceSegment_055_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1782 13 14, g32p_row02_traceSegment_055_1782_0013, g32p_row02_traceSegment_055_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1809 13 14, g32p_row02_traceSegment_055_1809_0013, g32p_row02_traceSegment_055_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1782 27 27, g32p_row02_traceSegment_055_1782_0027, g32p_row02_traceSegment_055_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1728 54 54, g32p_row02_traceSegment_055_1728_0054, g32p_row02_traceSegment_055_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1836 13 14, g32p_row02_traceSegment_055_1836_0013, g32p_row02_traceSegment_055_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1863 13 14, g32p_row02_traceSegment_055_1863_0013, g32p_row02_traceSegment_055_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1836 27 27, g32p_row02_traceSegment_055_1836_0027, g32p_row02_traceSegment_055_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1890 13 14, g32p_row02_traceSegment_055_1890_0013, g32p_row02_traceSegment_055_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1917 13 14, g32p_row02_traceSegment_055_1917_0013, g32p_row02_traceSegment_055_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1890 27 27, g32p_row02_traceSegment_055_1890_0027, g32p_row02_traceSegment_055_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1836 54 54, g32p_row02_traceSegment_055_1836_0054, g32p_row02_traceSegment_055_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1728 108 108, g32p_row02_traceSegment_055_1728_0108, g32p_row02_traceSegment_055_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1944 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1957 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1944 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1944 13 14, g32p_row02_traceSegment_055_1944_0013, g32p_row02_traceSegment_055_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1971 13 14, g32p_row02_traceSegment_055_1971_0013, g32p_row02_traceSegment_055_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1944 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1944 27 27, g32p_row02_traceSegment_055_1944_0027, g32p_row02_traceSegment_055_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1998 13 14, g32p_row02_traceSegment_055_1998_0013, g32p_row02_traceSegment_055_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2025 13 14, g32p_row02_traceSegment_055_2025_0013, g32p_row02_traceSegment_055_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1998 27 27, g32p_row02_traceSegment_055_1998_0027, g32p_row02_traceSegment_055_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 1944 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1944 54 54, g32p_row02_traceSegment_055_1944_0054, g32p_row02_traceSegment_055_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2052 13 14, g32p_row02_traceSegment_055_2052_0013, g32p_row02_traceSegment_055_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2079 13 14, g32p_row02_traceSegment_055_2079_0013, g32p_row02_traceSegment_055_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2052 27 27, g32p_row02_traceSegment_055_2052_0027, g32p_row02_traceSegment_055_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2106 13 14, g32p_row02_traceSegment_055_2106_0013, g32p_row02_traceSegment_055_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2133 13 14, g32p_row02_traceSegment_055_2133_0013, g32p_row02_traceSegment_055_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2106 27 27, g32p_row02_traceSegment_055_2106_0027, g32p_row02_traceSegment_055_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2052 54 54, g32p_row02_traceSegment_055_2052_0054, g32p_row02_traceSegment_055_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 1944 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1944 108 108, g32p_row02_traceSegment_055_1944_0108, g32p_row02_traceSegment_055_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1728 216 216, g32p_row02_traceSegment_055_1728_0216, g32p_row02_traceSegment_055_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2160 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2173 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2160 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2160 13 14, g32p_row02_traceSegment_055_2160_0013, g32p_row02_traceSegment_055_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2187 13 14, g32p_row02_traceSegment_055_2187_0013, g32p_row02_traceSegment_055_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2160 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2160 27 27, g32p_row02_traceSegment_055_2160_0027, g32p_row02_traceSegment_055_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2214 13 14, g32p_row02_traceSegment_055_2214_0013, g32p_row02_traceSegment_055_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2241 13 14, g32p_row02_traceSegment_055_2241_0013, g32p_row02_traceSegment_055_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2214 27 27, g32p_row02_traceSegment_055_2214_0027, g32p_row02_traceSegment_055_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2160 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2160 54 54, g32p_row02_traceSegment_055_2160_0054, g32p_row02_traceSegment_055_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2268 13 14, g32p_row02_traceSegment_055_2268_0013, g32p_row02_traceSegment_055_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2295 13 14, g32p_row02_traceSegment_055_2295_0013, g32p_row02_traceSegment_055_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2268 27 27, g32p_row02_traceSegment_055_2268_0027, g32p_row02_traceSegment_055_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2322 13 14, g32p_row02_traceSegment_055_2322_0013, g32p_row02_traceSegment_055_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2349 13 14, g32p_row02_traceSegment_055_2349_0013, g32p_row02_traceSegment_055_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2322 27 27, g32p_row02_traceSegment_055_2322_0027, g32p_row02_traceSegment_055_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2268 54 54, g32p_row02_traceSegment_055_2268_0054, g32p_row02_traceSegment_055_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 2160 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2160 108 108, g32p_row02_traceSegment_055_2160_0108, g32p_row02_traceSegment_055_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2376 13 14, g32p_row02_traceSegment_055_2376_0013, g32p_row02_traceSegment_055_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2403 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2403 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2403 13 14, g32p_row02_traceSegment_055_2403_0013, g32p_row02_traceSegment_055_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2376 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2376 27 27, g32p_row02_traceSegment_055_2376_0027, g32p_row02_traceSegment_055_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2430 13 14, g32p_row02_traceSegment_055_2430_0013, g32p_row02_traceSegment_055_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2457 13 14, g32p_row02_traceSegment_055_2457_0013, g32p_row02_traceSegment_055_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2430 27 27, g32p_row02_traceSegment_055_2430_0027, g32p_row02_traceSegment_055_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2376 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2376 54 54, g32p_row02_traceSegment_055_2376_0054, g32p_row02_traceSegment_055_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2484 13 14, g32p_row02_traceSegment_055_2484_0013, g32p_row02_traceSegment_055_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2511 13 14, g32p_row02_traceSegment_055_2511_0013, g32p_row02_traceSegment_055_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2484 27 27, g32p_row02_traceSegment_055_2484_0027, g32p_row02_traceSegment_055_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2538 13 14, g32p_row02_traceSegment_055_2538_0013, g32p_row02_traceSegment_055_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2565 13 14, g32p_row02_traceSegment_055_2565_0013, g32p_row02_traceSegment_055_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2538 27 27, g32p_row02_traceSegment_055_2538_0027, g32p_row02_traceSegment_055_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2484 54 54, g32p_row02_traceSegment_055_2484_0054, g32p_row02_traceSegment_055_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 2376 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2376 108 108, g32p_row02_traceSegment_055_2376_0108, g32p_row02_traceSegment_055_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 2160 432 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2160 216 216, g32p_row02_traceSegment_055_2160_0216, g32p_row02_traceSegment_055_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 864 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1728 432 432, g32p_row02_traceSegment_055_1728_0432, g32p_row02_traceSegment_055_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2592 13 14, g32p_row02_traceSegment_055_2592_0013, g32p_row02_traceSegment_055_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2619 13 14, g32p_row02_traceSegment_055_2619_0013, g32p_row02_traceSegment_055_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2592 27 27, g32p_row02_traceSegment_055_2592_0027, g32p_row02_traceSegment_055_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2646 13 14, g32p_row02_traceSegment_055_2646_0013, g32p_row02_traceSegment_055_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2673 13 14, g32p_row02_traceSegment_055_2673_0013, g32p_row02_traceSegment_055_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2646 27 27, g32p_row02_traceSegment_055_2646_0027, g32p_row02_traceSegment_055_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2592 54 54, g32p_row02_traceSegment_055_2592_0054, g32p_row02_traceSegment_055_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2700 13 14, g32p_row02_traceSegment_055_2700_0013, g32p_row02_traceSegment_055_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2727 13 14, g32p_row02_traceSegment_055_2727_0013, g32p_row02_traceSegment_055_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2700 27 27, g32p_row02_traceSegment_055_2700_0027, g32p_row02_traceSegment_055_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2754 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2767 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2754 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2754 13 14, g32p_row02_traceSegment_055_2754_0013, g32p_row02_traceSegment_055_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2794 14 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2781 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2781 13 14, g32p_row02_traceSegment_055_2781_0013, g32p_row02_traceSegment_055_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2754 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2754 27 27, g32p_row02_traceSegment_055_2754_0027, g32p_row02_traceSegment_055_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2700 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2700 54 54, g32p_row02_traceSegment_055_2700_0054, g32p_row02_traceSegment_055_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 2592 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2592 108 108, g32p_row02_traceSegment_055_2592_0108, g32p_row02_traceSegment_055_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2808 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2808 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2808 13 14, g32p_row02_traceSegment_055_2808_0013, g32p_row02_traceSegment_055_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2835 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2835 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2835 13 14, g32p_row02_traceSegment_055_2835_0013, g32p_row02_traceSegment_055_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2808 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2808 27 27, g32p_row02_traceSegment_055_2808_0027, g32p_row02_traceSegment_055_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2875 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2862 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2862 13 14, g32p_row02_traceSegment_055_2862_0013, g32p_row02_traceSegment_055_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2889 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2902 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2889 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2889 13 14, g32p_row02_traceSegment_055_2889_0013, g32p_row02_traceSegment_055_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2862 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2862 27 27, g32p_row02_traceSegment_055_2862_0027, g32p_row02_traceSegment_055_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2808 108 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2808 54 54, g32p_row02_traceSegment_055_2808_0054, g32p_row02_traceSegment_055_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2929 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2916 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2916 13 14, g32p_row02_traceSegment_055_2916_0013, g32p_row02_traceSegment_055_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2943 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2943 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2943 13 14, g32p_row02_traceSegment_055_2943_0013, g32p_row02_traceSegment_055_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2916 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2916 27 27, g32p_row02_traceSegment_055_2916_0027, g32p_row02_traceSegment_055_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2970 13 14, g32p_row02_traceSegment_055_2970_0013, g32p_row02_traceSegment_055_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2997 13 14, g32p_row02_traceSegment_055_2997_0013, g32p_row02_traceSegment_055_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2970 27 27, g32p_row02_traceSegment_055_2970_0027, g32p_row02_traceSegment_055_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 2916 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2916 54 54, g32p_row02_traceSegment_055_2916_0054, g32p_row02_traceSegment_055_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 2808 216 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2808 108 108, g32p_row02_traceSegment_055_2808_0108, g32p_row02_traceSegment_055_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 2592 432 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2592 216 216, g32p_row02_traceSegment_055_2592_0216, g32p_row02_traceSegment_055_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3024 13 14, g32p_row02_traceSegment_055_3024_0013, g32p_row02_traceSegment_055_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3051 13 14, g32p_row02_traceSegment_055_3051_0013, g32p_row02_traceSegment_055_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3024 27 27, g32p_row02_traceSegment_055_3024_0027, g32p_row02_traceSegment_055_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3078 13 14, g32p_row02_traceSegment_055_3078_0013, g32p_row02_traceSegment_055_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3105 13 14, g32p_row02_traceSegment_055_3105_0013, g32p_row02_traceSegment_055_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3078 27 27, g32p_row02_traceSegment_055_3078_0027, g32p_row02_traceSegment_055_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3024 54 54, g32p_row02_traceSegment_055_3024_0054, g32p_row02_traceSegment_055_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3132 13 14, g32p_row02_traceSegment_055_3132_0013, g32p_row02_traceSegment_055_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3172 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3159 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3159 13 14, g32p_row02_traceSegment_055_3159_0013, g32p_row02_traceSegment_055_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3132 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3132 27 27, g32p_row02_traceSegment_055_3132_0027, g32p_row02_traceSegment_055_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3186 13 14, g32p_row02_traceSegment_055_3186_0013, g32p_row02_traceSegment_055_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3213 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3226 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3213 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3213 13 14, g32p_row02_traceSegment_055_3213_0013, g32p_row02_traceSegment_055_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3186 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3186 27 27, g32p_row02_traceSegment_055_3186_0027, g32p_row02_traceSegment_055_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 3132 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3132 54 54, g32p_row02_traceSegment_055_3132_0054, g32p_row02_traceSegment_055_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 3024 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3024 108 108, g32p_row02_traceSegment_055_3024_0108, g32p_row02_traceSegment_055_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3240 13 14, g32p_row02_traceSegment_055_3240_0013, g32p_row02_traceSegment_055_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3267 13 14, g32p_row02_traceSegment_055_3267_0013, g32p_row02_traceSegment_055_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3240 27 27, g32p_row02_traceSegment_055_3240_0027, g32p_row02_traceSegment_055_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3294 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3294 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3294 13 14, g32p_row02_traceSegment_055_3294_0013, g32p_row02_traceSegment_055_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3334 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3321 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3321 13 14, g32p_row02_traceSegment_055_3321_0013, g32p_row02_traceSegment_055_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3294 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3294 27 27, g32p_row02_traceSegment_055_3294_0027, g32p_row02_traceSegment_055_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 3240 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3240 54 54, g32p_row02_traceSegment_055_3240_0054, g32p_row02_traceSegment_055_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3348 13 14, g32p_row02_traceSegment_055_3348_0013, g32p_row02_traceSegment_055_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3375 13 14, g32p_row02_traceSegment_055_3375_0013, g32p_row02_traceSegment_055_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3348 27 27, g32p_row02_traceSegment_055_3348_0027, g32p_row02_traceSegment_055_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3415 14 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3402 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3402 13 14, g32p_row02_traceSegment_055_3402_0013, g32p_row02_traceSegment_055_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_055 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_055 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_055_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_055 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3429 13 14, g32p_row02_traceSegment_055_3429_0013, g32p_row02_traceSegment_055_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_055 3402 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3402 27 27, g32p_row02_traceSegment_055_3402_0027, g32p_row02_traceSegment_055_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_055 3348 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3348 54 54, g32p_row02_traceSegment_055_3348_0054, g32p_row02_traceSegment_055_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_055 3240 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3240 108 108, g32p_row02_traceSegment_055_3240_0108, g32p_row02_traceSegment_055_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_055_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_055 3024 432 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 3024 216 216, g32p_row02_traceSegment_055_3024_0216, g32p_row02_traceSegment_055_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_055_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_055 2592 864 = [0, 0, 0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 2592 432 432, g32p_row02_traceSegment_055_2592_0432, g32p_row02_traceSegment_055_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_055_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_055 1728 1728 = [0, 0, 0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 1728 864 864, g32p_row02_traceSegment_055_1728_0864, g32p_row02_traceSegment_055_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_055_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_055 0 3456 = [0, 0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_055 0 1728 1728, g32p_row02_traceSegment_055_0000_1728, g32p_row02_traceSegment_055_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_055 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 55 = [0, 0, 0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_055_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_056_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 13 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 0 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 13 14, g32p_row02_traceSegment_056_0000_0013, g32p_row02_traceSegment_056_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 27 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 27 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 27 13 14, g32p_row02_traceSegment_056_0027_0013, g32p_row02_traceSegment_056_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 0 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 27 27, g32p_row02_traceSegment_056_0000_0027, g32p_row02_traceSegment_056_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 54 13 14, g32p_row02_traceSegment_056_0054_0013, g32p_row02_traceSegment_056_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 81 13 14, g32p_row02_traceSegment_056_0081_0013, g32p_row02_traceSegment_056_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 54 27 27, g32p_row02_traceSegment_056_0054_0027, g32p_row02_traceSegment_056_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 0 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 54 54, g32p_row02_traceSegment_056_0000_0054, g32p_row02_traceSegment_056_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 108 13 14, g32p_row02_traceSegment_056_0108_0013, g32p_row02_traceSegment_056_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 135 13 14, g32p_row02_traceSegment_056_0135_0013, g32p_row02_traceSegment_056_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 108 27 27, g32p_row02_traceSegment_056_0108_0027, g32p_row02_traceSegment_056_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 162 13 14, g32p_row02_traceSegment_056_0162_0013, g32p_row02_traceSegment_056_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 202 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 189 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 189 13 14, g32p_row02_traceSegment_056_0189_0013, g32p_row02_traceSegment_056_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 162 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 162 27 27, g32p_row02_traceSegment_056_0162_0027, g32p_row02_traceSegment_056_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 108 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 108 54 54, g32p_row02_traceSegment_056_0108_0054, g32p_row02_traceSegment_056_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 0 216 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 108 108, g32p_row02_traceSegment_056_0000_0108, g32p_row02_traceSegment_056_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 229 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 216 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 216 13 14, g32p_row02_traceSegment_056_0216_0013, g32p_row02_traceSegment_056_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 243 13 14, g32p_row02_traceSegment_056_0243_0013, g32p_row02_traceSegment_056_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 216 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 216 27 27, g32p_row02_traceSegment_056_0216_0027, g32p_row02_traceSegment_056_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 270 13 14, g32p_row02_traceSegment_056_0270_0013, g32p_row02_traceSegment_056_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 297 13 14, g32p_row02_traceSegment_056_0297_0013, g32p_row02_traceSegment_056_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 270 27 27, g32p_row02_traceSegment_056_0270_0027, g32p_row02_traceSegment_056_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 216 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 216 54 54, g32p_row02_traceSegment_056_0216_0054, g32p_row02_traceSegment_056_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 324 13 14, g32p_row02_traceSegment_056_0324_0013, g32p_row02_traceSegment_056_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 351 13 14, g32p_row02_traceSegment_056_0351_0013, g32p_row02_traceSegment_056_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 324 27 27, g32p_row02_traceSegment_056_0324_0027, g32p_row02_traceSegment_056_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 378 13 14, g32p_row02_traceSegment_056_0378_0013, g32p_row02_traceSegment_056_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 405 13 14, g32p_row02_traceSegment_056_0405_0013, g32p_row02_traceSegment_056_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 378 27 27, g32p_row02_traceSegment_056_0378_0027, g32p_row02_traceSegment_056_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 324 54 54, g32p_row02_traceSegment_056_0324_0054, g32p_row02_traceSegment_056_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 216 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 216 108 108, g32p_row02_traceSegment_056_0216_0108, g32p_row02_traceSegment_056_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 0 432 = [2, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 216 216, g32p_row02_traceSegment_056_0000_0216, g32p_row02_traceSegment_056_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 432 13 14, g32p_row02_traceSegment_056_0432_0013, g32p_row02_traceSegment_056_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 459 13 14, g32p_row02_traceSegment_056_0459_0013, g32p_row02_traceSegment_056_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 432 27 27, g32p_row02_traceSegment_056_0432_0027, g32p_row02_traceSegment_056_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 486 13 14, g32p_row02_traceSegment_056_0486_0013, g32p_row02_traceSegment_056_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 513 13 14, g32p_row02_traceSegment_056_0513_0013, g32p_row02_traceSegment_056_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 486 27 27, g32p_row02_traceSegment_056_0486_0027, g32p_row02_traceSegment_056_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 432 54 54, g32p_row02_traceSegment_056_0432_0054, g32p_row02_traceSegment_056_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 540 13 14, g32p_row02_traceSegment_056_0540_0013, g32p_row02_traceSegment_056_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 567 13 14, g32p_row02_traceSegment_056_0567_0013, g32p_row02_traceSegment_056_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 540 27 27, g32p_row02_traceSegment_056_0540_0027, g32p_row02_traceSegment_056_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 594 13 14, g32p_row02_traceSegment_056_0594_0013, g32p_row02_traceSegment_056_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 621 13 14, g32p_row02_traceSegment_056_0621_0013, g32p_row02_traceSegment_056_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 594 27 27, g32p_row02_traceSegment_056_0594_0027, g32p_row02_traceSegment_056_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 540 54 54, g32p_row02_traceSegment_056_0540_0054, g32p_row02_traceSegment_056_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 432 108 108, g32p_row02_traceSegment_056_0432_0108, g32p_row02_traceSegment_056_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 648 13 14, g32p_row02_traceSegment_056_0648_0013, g32p_row02_traceSegment_056_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 688 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 675 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 675 13 14, g32p_row02_traceSegment_056_0675_0013, g32p_row02_traceSegment_056_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 648 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 648 27 27, g32p_row02_traceSegment_056_0648_0027, g32p_row02_traceSegment_056_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 715 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 702 13 14, g32p_row02_traceSegment_056_0702_0013, g32p_row02_traceSegment_056_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 729 13 14, g32p_row02_traceSegment_056_0729_0013, g32p_row02_traceSegment_056_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 702 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 702 27 27, g32p_row02_traceSegment_056_0702_0027, g32p_row02_traceSegment_056_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 648 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 648 54 54, g32p_row02_traceSegment_056_0648_0054, g32p_row02_traceSegment_056_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 756 13 14, g32p_row02_traceSegment_056_0756_0013, g32p_row02_traceSegment_056_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 796 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 783 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 783 13 14, g32p_row02_traceSegment_056_0783_0013, g32p_row02_traceSegment_056_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 756 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 756 27 27, g32p_row02_traceSegment_056_0756_0027, g32p_row02_traceSegment_056_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 823 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 810 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 810 13 14, g32p_row02_traceSegment_056_0810_0013, g32p_row02_traceSegment_056_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 850 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 837 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 837 13 14, g32p_row02_traceSegment_056_0837_0013, g32p_row02_traceSegment_056_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 810 54 = [1, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 810 27 27, g32p_row02_traceSegment_056_0810_0027, g32p_row02_traceSegment_056_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 756 108 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 756 54 54, g32p_row02_traceSegment_056_0756_0054, g32p_row02_traceSegment_056_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 648 216 = [1, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 648 108 108, g32p_row02_traceSegment_056_0648_0108, g32p_row02_traceSegment_056_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 432 432 = [1, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 432 216 216, g32p_row02_traceSegment_056_0432_0216, g32p_row02_traceSegment_056_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_056 0 864 = [3, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 432 432, g32p_row02_traceSegment_056_0000_0432, g32p_row02_traceSegment_056_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 877 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 864 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 864 13 14, g32p_row02_traceSegment_056_0864_0013, g32p_row02_traceSegment_056_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 891 13 14, g32p_row02_traceSegment_056_0891_0013, g32p_row02_traceSegment_056_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 864 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 864 27 27, g32p_row02_traceSegment_056_0864_0027, g32p_row02_traceSegment_056_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 918 13 14, g32p_row02_traceSegment_056_0918_0013, g32p_row02_traceSegment_056_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 945 13 14, g32p_row02_traceSegment_056_0945_0013, g32p_row02_traceSegment_056_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 918 27 27, g32p_row02_traceSegment_056_0918_0027, g32p_row02_traceSegment_056_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 864 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 864 54 54, g32p_row02_traceSegment_056_0864_0054, g32p_row02_traceSegment_056_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 972 13 14, g32p_row02_traceSegment_056_0972_0013, g32p_row02_traceSegment_056_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 999 13 14, g32p_row02_traceSegment_056_0999_0013, g32p_row02_traceSegment_056_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 972 27 27, g32p_row02_traceSegment_056_0972_0027, g32p_row02_traceSegment_056_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1026 13 14, g32p_row02_traceSegment_056_1026_0013, g32p_row02_traceSegment_056_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1053 13 14, g32p_row02_traceSegment_056_1053_0013, g32p_row02_traceSegment_056_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1026 27 27, g32p_row02_traceSegment_056_1026_0027, g32p_row02_traceSegment_056_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 972 54 54, g32p_row02_traceSegment_056_0972_0054, g32p_row02_traceSegment_056_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 864 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 864 108 108, g32p_row02_traceSegment_056_0864_0108, g32p_row02_traceSegment_056_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1080 13 14, g32p_row02_traceSegment_056_1080_0013, g32p_row02_traceSegment_056_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1107 13 14, g32p_row02_traceSegment_056_1107_0013, g32p_row02_traceSegment_056_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1080 27 27, g32p_row02_traceSegment_056_1080_0027, g32p_row02_traceSegment_056_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1134 13 14, g32p_row02_traceSegment_056_1134_0013, g32p_row02_traceSegment_056_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1161 13 14, g32p_row02_traceSegment_056_1161_0013, g32p_row02_traceSegment_056_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1134 27 27, g32p_row02_traceSegment_056_1134_0027, g32p_row02_traceSegment_056_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1080 54 54, g32p_row02_traceSegment_056_1080_0054, g32p_row02_traceSegment_056_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1188 13 14, g32p_row02_traceSegment_056_1188_0013, g32p_row02_traceSegment_056_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1215 13 14, g32p_row02_traceSegment_056_1215_0013, g32p_row02_traceSegment_056_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1188 27 27, g32p_row02_traceSegment_056_1188_0027, g32p_row02_traceSegment_056_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1242 13 14, g32p_row02_traceSegment_056_1242_0013, g32p_row02_traceSegment_056_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1269 13 14, g32p_row02_traceSegment_056_1269_0013, g32p_row02_traceSegment_056_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1242 27 27, g32p_row02_traceSegment_056_1242_0027, g32p_row02_traceSegment_056_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1188 54 54, g32p_row02_traceSegment_056_1188_0054, g32p_row02_traceSegment_056_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1080 108 108, g32p_row02_traceSegment_056_1080_0108, g32p_row02_traceSegment_056_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 864 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 864 216 216, g32p_row02_traceSegment_056_0864_0216, g32p_row02_traceSegment_056_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1296 13 14, g32p_row02_traceSegment_056_1296_0013, g32p_row02_traceSegment_056_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1323 13 14, g32p_row02_traceSegment_056_1323_0013, g32p_row02_traceSegment_056_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1296 27 27, g32p_row02_traceSegment_056_1296_0027, g32p_row02_traceSegment_056_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1350 13 14, g32p_row02_traceSegment_056_1350_0013, g32p_row02_traceSegment_056_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1377 13 14, g32p_row02_traceSegment_056_1377_0013, g32p_row02_traceSegment_056_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1350 27 27, g32p_row02_traceSegment_056_1350_0027, g32p_row02_traceSegment_056_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1296 54 54, g32p_row02_traceSegment_056_1296_0054, g32p_row02_traceSegment_056_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1404 13 14, g32p_row02_traceSegment_056_1404_0013, g32p_row02_traceSegment_056_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1431 13 14, g32p_row02_traceSegment_056_1431_0013, g32p_row02_traceSegment_056_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1404 27 27, g32p_row02_traceSegment_056_1404_0027, g32p_row02_traceSegment_056_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1458 13 14, g32p_row02_traceSegment_056_1458_0013, g32p_row02_traceSegment_056_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1485 13 14, g32p_row02_traceSegment_056_1485_0013, g32p_row02_traceSegment_056_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1458 27 27, g32p_row02_traceSegment_056_1458_0027, g32p_row02_traceSegment_056_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1404 54 54, g32p_row02_traceSegment_056_1404_0054, g32p_row02_traceSegment_056_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1296 108 108, g32p_row02_traceSegment_056_1296_0108, g32p_row02_traceSegment_056_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1512 13 14, g32p_row02_traceSegment_056_1512_0013, g32p_row02_traceSegment_056_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1539 13 14, g32p_row02_traceSegment_056_1539_0013, g32p_row02_traceSegment_056_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1512 27 27, g32p_row02_traceSegment_056_1512_0027, g32p_row02_traceSegment_056_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1566 13 14, g32p_row02_traceSegment_056_1566_0013, g32p_row02_traceSegment_056_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1593 13 14, g32p_row02_traceSegment_056_1593_0013, g32p_row02_traceSegment_056_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1566 27 27, g32p_row02_traceSegment_056_1566_0027, g32p_row02_traceSegment_056_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1512 54 54, g32p_row02_traceSegment_056_1512_0054, g32p_row02_traceSegment_056_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1620 13 14, g32p_row02_traceSegment_056_1620_0013, g32p_row02_traceSegment_056_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1647 13 14, g32p_row02_traceSegment_056_1647_0013, g32p_row02_traceSegment_056_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1620 27 27, g32p_row02_traceSegment_056_1620_0027, g32p_row02_traceSegment_056_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1674 13 14, g32p_row02_traceSegment_056_1674_0013, g32p_row02_traceSegment_056_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1701 13 14, g32p_row02_traceSegment_056_1701_0013, g32p_row02_traceSegment_056_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1674 27 27, g32p_row02_traceSegment_056_1674_0027, g32p_row02_traceSegment_056_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1620 54 54, g32p_row02_traceSegment_056_1620_0054, g32p_row02_traceSegment_056_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1512 108 108, g32p_row02_traceSegment_056_1512_0108, g32p_row02_traceSegment_056_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1296 216 216, g32p_row02_traceSegment_056_1296_0216, g32p_row02_traceSegment_056_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_056 864 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 864 432 432, g32p_row02_traceSegment_056_0864_0432, g32p_row02_traceSegment_056_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_056 0 1728 = [4, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 864 864, g32p_row02_traceSegment_056_0000_0864, g32p_row02_traceSegment_056_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1728 13 14, g32p_row02_traceSegment_056_1728_0013, g32p_row02_traceSegment_056_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1755 13 14, g32p_row02_traceSegment_056_1755_0013, g32p_row02_traceSegment_056_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1728 27 27, g32p_row02_traceSegment_056_1728_0027, g32p_row02_traceSegment_056_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1782 13 14, g32p_row02_traceSegment_056_1782_0013, g32p_row02_traceSegment_056_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1809 13 14, g32p_row02_traceSegment_056_1809_0013, g32p_row02_traceSegment_056_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1782 27 27, g32p_row02_traceSegment_056_1782_0027, g32p_row02_traceSegment_056_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1728 54 54, g32p_row02_traceSegment_056_1728_0054, g32p_row02_traceSegment_056_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1836 13 14, g32p_row02_traceSegment_056_1836_0013, g32p_row02_traceSegment_056_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1863 13 14, g32p_row02_traceSegment_056_1863_0013, g32p_row02_traceSegment_056_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1836 27 27, g32p_row02_traceSegment_056_1836_0027, g32p_row02_traceSegment_056_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1890 13 14, g32p_row02_traceSegment_056_1890_0013, g32p_row02_traceSegment_056_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1917 13 14, g32p_row02_traceSegment_056_1917_0013, g32p_row02_traceSegment_056_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1890 27 27, g32p_row02_traceSegment_056_1890_0027, g32p_row02_traceSegment_056_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1836 54 54, g32p_row02_traceSegment_056_1836_0054, g32p_row02_traceSegment_056_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1728 108 108, g32p_row02_traceSegment_056_1728_0108, g32p_row02_traceSegment_056_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1944 13 14, g32p_row02_traceSegment_056_1944_0013, g32p_row02_traceSegment_056_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1971 13 14, g32p_row02_traceSegment_056_1971_0013, g32p_row02_traceSegment_056_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1944 27 27, g32p_row02_traceSegment_056_1944_0027, g32p_row02_traceSegment_056_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2011 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 1998 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1998 13 14, g32p_row02_traceSegment_056_1998_0013, g32p_row02_traceSegment_056_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2025 13 14, g32p_row02_traceSegment_056_2025_0013, g32p_row02_traceSegment_056_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 1998 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1998 27 27, g32p_row02_traceSegment_056_1998_0027, g32p_row02_traceSegment_056_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 1944 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1944 54 54, g32p_row02_traceSegment_056_1944_0054, g32p_row02_traceSegment_056_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2052 13 14, g32p_row02_traceSegment_056_2052_0013, g32p_row02_traceSegment_056_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2092 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2079 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2079 13 14, g32p_row02_traceSegment_056_2079_0013, g32p_row02_traceSegment_056_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2052 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2052 27 27, g32p_row02_traceSegment_056_2052_0027, g32p_row02_traceSegment_056_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2119 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2106 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2106 13 14, g32p_row02_traceSegment_056_2106_0013, g32p_row02_traceSegment_056_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2133 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2146 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2133 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2133 13 14, g32p_row02_traceSegment_056_2133_0013, g32p_row02_traceSegment_056_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2106 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2106 27 27, g32p_row02_traceSegment_056_2106_0027, g32p_row02_traceSegment_056_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2052 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2052 54 54, g32p_row02_traceSegment_056_2052_0054, g32p_row02_traceSegment_056_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 1944 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1944 108 108, g32p_row02_traceSegment_056_1944_0108, g32p_row02_traceSegment_056_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 432 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1728 216 216, g32p_row02_traceSegment_056_1728_0216, g32p_row02_traceSegment_056_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2160 13 14, g32p_row02_traceSegment_056_2160_0013, g32p_row02_traceSegment_056_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2187 13 14, g32p_row02_traceSegment_056_2187_0013, g32p_row02_traceSegment_056_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2160 27 27, g32p_row02_traceSegment_056_2160_0027, g32p_row02_traceSegment_056_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2214 13 14, g32p_row02_traceSegment_056_2214_0013, g32p_row02_traceSegment_056_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2241 13 14, g32p_row02_traceSegment_056_2241_0013, g32p_row02_traceSegment_056_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2214 27 27, g32p_row02_traceSegment_056_2214_0027, g32p_row02_traceSegment_056_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2160 54 54, g32p_row02_traceSegment_056_2160_0054, g32p_row02_traceSegment_056_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2268 13 14, g32p_row02_traceSegment_056_2268_0013, g32p_row02_traceSegment_056_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2295 13 14, g32p_row02_traceSegment_056_2295_0013, g32p_row02_traceSegment_056_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2268 27 27, g32p_row02_traceSegment_056_2268_0027, g32p_row02_traceSegment_056_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2322 13 14, g32p_row02_traceSegment_056_2322_0013, g32p_row02_traceSegment_056_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2349 13 14, g32p_row02_traceSegment_056_2349_0013, g32p_row02_traceSegment_056_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2322 27 27, g32p_row02_traceSegment_056_2322_0027, g32p_row02_traceSegment_056_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2268 54 54, g32p_row02_traceSegment_056_2268_0054, g32p_row02_traceSegment_056_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2160 108 108, g32p_row02_traceSegment_056_2160_0108, g32p_row02_traceSegment_056_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2376 13 14, g32p_row02_traceSegment_056_2376_0013, g32p_row02_traceSegment_056_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2403 13 14, g32p_row02_traceSegment_056_2403_0013, g32p_row02_traceSegment_056_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2376 27 27, g32p_row02_traceSegment_056_2376_0027, g32p_row02_traceSegment_056_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2430 13 14, g32p_row02_traceSegment_056_2430_0013, g32p_row02_traceSegment_056_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2457 13 14, g32p_row02_traceSegment_056_2457_0013, g32p_row02_traceSegment_056_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2430 27 27, g32p_row02_traceSegment_056_2430_0027, g32p_row02_traceSegment_056_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2376 54 54, g32p_row02_traceSegment_056_2376_0054, g32p_row02_traceSegment_056_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2484 13 14, g32p_row02_traceSegment_056_2484_0013, g32p_row02_traceSegment_056_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2511 13 14, g32p_row02_traceSegment_056_2511_0013, g32p_row02_traceSegment_056_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2484 27 27, g32p_row02_traceSegment_056_2484_0027, g32p_row02_traceSegment_056_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2538 13 14, g32p_row02_traceSegment_056_2538_0013, g32p_row02_traceSegment_056_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2578 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2565 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2565 13 14, g32p_row02_traceSegment_056_2565_0013, g32p_row02_traceSegment_056_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2538 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2538 27 27, g32p_row02_traceSegment_056_2538_0027, g32p_row02_traceSegment_056_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2484 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2484 54 54, g32p_row02_traceSegment_056_2484_0054, g32p_row02_traceSegment_056_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 2376 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2376 108 108, g32p_row02_traceSegment_056_2376_0108, g32p_row02_traceSegment_056_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 2160 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2160 216 216, g32p_row02_traceSegment_056_2160_0216, g32p_row02_traceSegment_056_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 864 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1728 432 432, g32p_row02_traceSegment_056_1728_0432, g32p_row02_traceSegment_056_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2592 13 14, g32p_row02_traceSegment_056_2592_0013, g32p_row02_traceSegment_056_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2632 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2619 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2619 13 14, g32p_row02_traceSegment_056_2619_0013, g32p_row02_traceSegment_056_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2592 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2592 27 27, g32p_row02_traceSegment_056_2592_0027, g32p_row02_traceSegment_056_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2646 13 14, g32p_row02_traceSegment_056_2646_0013, g32p_row02_traceSegment_056_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2673 13 14, g32p_row02_traceSegment_056_2673_0013, g32p_row02_traceSegment_056_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2646 27 27, g32p_row02_traceSegment_056_2646_0027, g32p_row02_traceSegment_056_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2592 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2592 54 54, g32p_row02_traceSegment_056_2592_0054, g32p_row02_traceSegment_056_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2700 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2700 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2700 13 14, g32p_row02_traceSegment_056_2700_0013, g32p_row02_traceSegment_056_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2727 13 14, g32p_row02_traceSegment_056_2727_0013, g32p_row02_traceSegment_056_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2700 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2700 27 27, g32p_row02_traceSegment_056_2700_0027, g32p_row02_traceSegment_056_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2754 13 14, g32p_row02_traceSegment_056_2754_0013, g32p_row02_traceSegment_056_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2781 13 14, g32p_row02_traceSegment_056_2781_0013, g32p_row02_traceSegment_056_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2754 27 27, g32p_row02_traceSegment_056_2754_0027, g32p_row02_traceSegment_056_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2700 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2700 54 54, g32p_row02_traceSegment_056_2700_0054, g32p_row02_traceSegment_056_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 2592 216 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2592 108 108, g32p_row02_traceSegment_056_2592_0108, g32p_row02_traceSegment_056_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2808 13 14, g32p_row02_traceSegment_056_2808_0013, g32p_row02_traceSegment_056_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2835 13 14, g32p_row02_traceSegment_056_2835_0013, g32p_row02_traceSegment_056_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2808 27 27, g32p_row02_traceSegment_056_2808_0027, g32p_row02_traceSegment_056_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2862 13 14, g32p_row02_traceSegment_056_2862_0013, g32p_row02_traceSegment_056_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2889 13 14, g32p_row02_traceSegment_056_2889_0013, g32p_row02_traceSegment_056_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2862 27 27, g32p_row02_traceSegment_056_2862_0027, g32p_row02_traceSegment_056_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2808 54 54, g32p_row02_traceSegment_056_2808_0054, g32p_row02_traceSegment_056_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2916 13 14, g32p_row02_traceSegment_056_2916_0013, g32p_row02_traceSegment_056_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2956 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2943 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2943 13 14, g32p_row02_traceSegment_056_2943_0013, g32p_row02_traceSegment_056_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2916 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2916 27 27, g32p_row02_traceSegment_056_2916_0027, g32p_row02_traceSegment_056_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2970 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2970 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2970 13 14, g32p_row02_traceSegment_056_2970_0013, g32p_row02_traceSegment_056_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 2997 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3010 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 2997 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2997 13 14, g32p_row02_traceSegment_056_2997_0013, g32p_row02_traceSegment_056_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 2970 54 = [1, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2970 27 27, g32p_row02_traceSegment_056_2970_0027, g32p_row02_traceSegment_056_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 2916 108 = [2, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2916 54 54, g32p_row02_traceSegment_056_2916_0054, g32p_row02_traceSegment_056_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 2808 216 = [2, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2808 108 108, g32p_row02_traceSegment_056_2808_0108, g32p_row02_traceSegment_056_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 2592 432 = [3, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2592 216 216, g32p_row02_traceSegment_056_2592_0216, g32p_row02_traceSegment_056_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3024 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3037 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3024 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3024 13 14, g32p_row02_traceSegment_056_3024_0013, g32p_row02_traceSegment_056_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3051 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3064 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3051 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3051 13 14, g32p_row02_traceSegment_056_3051_0013, g32p_row02_traceSegment_056_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3024 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3024 27 27, g32p_row02_traceSegment_056_3024_0027, g32p_row02_traceSegment_056_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3078 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3091 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3078 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3078 13 14, g32p_row02_traceSegment_056_3078_0013, g32p_row02_traceSegment_056_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3105 13 14, g32p_row02_traceSegment_056_3105_0013, g32p_row02_traceSegment_056_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3078 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3078 27 27, g32p_row02_traceSegment_056_3078_0027, g32p_row02_traceSegment_056_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 3024 108 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3024 54 54, g32p_row02_traceSegment_056_3024_0054, g32p_row02_traceSegment_056_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3132 13 14, g32p_row02_traceSegment_056_3132_0013, g32p_row02_traceSegment_056_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3159 13 14, g32p_row02_traceSegment_056_3159_0013, g32p_row02_traceSegment_056_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3132 27 27, g32p_row02_traceSegment_056_3132_0027, g32p_row02_traceSegment_056_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3186 13 14, g32p_row02_traceSegment_056_3186_0013, g32p_row02_traceSegment_056_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3213 13 14, g32p_row02_traceSegment_056_3213_0013, g32p_row02_traceSegment_056_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3186 27 27, g32p_row02_traceSegment_056_3186_0027, g32p_row02_traceSegment_056_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3132 54 54, g32p_row02_traceSegment_056_3132_0054, g32p_row02_traceSegment_056_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 3024 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3024 108 108, g32p_row02_traceSegment_056_3024_0108, g32p_row02_traceSegment_056_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3240 13 14, g32p_row02_traceSegment_056_3240_0013, g32p_row02_traceSegment_056_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3267 13 14, g32p_row02_traceSegment_056_3267_0013, g32p_row02_traceSegment_056_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3240 27 27, g32p_row02_traceSegment_056_3240_0027, g32p_row02_traceSegment_056_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3294 13 14, g32p_row02_traceSegment_056_3294_0013, g32p_row02_traceSegment_056_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3321 13 14, g32p_row02_traceSegment_056_3321_0013, g32p_row02_traceSegment_056_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3294 27 27, g32p_row02_traceSegment_056_3294_0027, g32p_row02_traceSegment_056_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3240 54 54, g32p_row02_traceSegment_056_3240_0054, g32p_row02_traceSegment_056_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3348 13 14, g32p_row02_traceSegment_056_3348_0013, g32p_row02_traceSegment_056_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3375 13 14, g32p_row02_traceSegment_056_3375_0013, g32p_row02_traceSegment_056_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3348 27 27, g32p_row02_traceSegment_056_3348_0027, g32p_row02_traceSegment_056_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3402 13 14, g32p_row02_traceSegment_056_3402_0013, g32p_row02_traceSegment_056_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_056 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_056 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_056_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_056 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3429 13 14, g32p_row02_traceSegment_056_3429_0013, g32p_row02_traceSegment_056_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_056 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3402 27 27, g32p_row02_traceSegment_056_3402_0027, g32p_row02_traceSegment_056_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_056 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3348 54 54, g32p_row02_traceSegment_056_3348_0054, g32p_row02_traceSegment_056_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_056 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3240 108 108, g32p_row02_traceSegment_056_3240_0108, g32p_row02_traceSegment_056_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_056_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_056 3024 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 3024 216 216, g32p_row02_traceSegment_056_3024_0216, g32p_row02_traceSegment_056_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_056_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_056 2592 864 = [3, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 2592 432 432, g32p_row02_traceSegment_056_2592_0432, g32p_row02_traceSegment_056_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_056_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_056 1728 1728 = [12, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 1728 864 864, g32p_row02_traceSegment_056_1728_0864, g32p_row02_traceSegment_056_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_056_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_056 0 3456 = [16, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_056 0 1728 1728, g32p_row02_traceSegment_056_0000_1728, g32p_row02_traceSegment_056_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 56 = [16, 0, 0, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_056_0000_3456

end HodgeLean.Foundations.Program

end
end
