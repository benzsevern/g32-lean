import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0300

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_046 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 46 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_046_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 13 14, g32p_row02_traceSegment_046_0000_0013, g32p_row02_traceSegment_046_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 27 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 27 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 27 13 14, g32p_row02_traceSegment_046_0027_0013, g32p_row02_traceSegment_046_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 0 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 27 27, g32p_row02_traceSegment_046_0000_0027, g32p_row02_traceSegment_046_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 54 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 67 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 54 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 54 13 14, g32p_row02_traceSegment_046_0054_0013, g32p_row02_traceSegment_046_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 81 13 14, g32p_row02_traceSegment_046_0081_0013, g32p_row02_traceSegment_046_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 54 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 54 27 27, g32p_row02_traceSegment_046_0054_0027, g32p_row02_traceSegment_046_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 0 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 54 54, g32p_row02_traceSegment_046_0000_0054, g32p_row02_traceSegment_046_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 108 13 14, g32p_row02_traceSegment_046_0108_0013, g32p_row02_traceSegment_046_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 135 13 14, g32p_row02_traceSegment_046_0135_0013, g32p_row02_traceSegment_046_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 108 27 27, g32p_row02_traceSegment_046_0108_0027, g32p_row02_traceSegment_046_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 162 13 14, g32p_row02_traceSegment_046_0162_0013, g32p_row02_traceSegment_046_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 189 13 14, g32p_row02_traceSegment_046_0189_0013, g32p_row02_traceSegment_046_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 162 27 27, g32p_row02_traceSegment_046_0162_0027, g32p_row02_traceSegment_046_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 108 54 54, g32p_row02_traceSegment_046_0108_0054, g32p_row02_traceSegment_046_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 0 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 108 108, g32p_row02_traceSegment_046_0000_0108, g32p_row02_traceSegment_046_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 229 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 216 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 216 13 14, g32p_row02_traceSegment_046_0216_0013, g32p_row02_traceSegment_046_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 243 13 14, g32p_row02_traceSegment_046_0243_0013, g32p_row02_traceSegment_046_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 216 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 216 27 27, g32p_row02_traceSegment_046_0216_0027, g32p_row02_traceSegment_046_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 270 13 14, g32p_row02_traceSegment_046_0270_0013, g32p_row02_traceSegment_046_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 297 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 310 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 297 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 297 13 14, g32p_row02_traceSegment_046_0297_0013, g32p_row02_traceSegment_046_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 270 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 270 27 27, g32p_row02_traceSegment_046_0270_0027, g32p_row02_traceSegment_046_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 216 108 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 216 54 54, g32p_row02_traceSegment_046_0216_0054, g32p_row02_traceSegment_046_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 324 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 324 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 324 13 14, g32p_row02_traceSegment_046_0324_0013, g32p_row02_traceSegment_046_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 351 13 14, g32p_row02_traceSegment_046_0351_0013, g32p_row02_traceSegment_046_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 324 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 324 27 27, g32p_row02_traceSegment_046_0324_0027, g32p_row02_traceSegment_046_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 378 13 14, g32p_row02_traceSegment_046_0378_0013, g32p_row02_traceSegment_046_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 405 13 14, g32p_row02_traceSegment_046_0405_0013, g32p_row02_traceSegment_046_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 378 27 27, g32p_row02_traceSegment_046_0378_0027, g32p_row02_traceSegment_046_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 324 108 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 324 54 54, g32p_row02_traceSegment_046_0324_0054, g32p_row02_traceSegment_046_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 216 216 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 216 108 108, g32p_row02_traceSegment_046_0216_0108, g32p_row02_traceSegment_046_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 0 432 = [0, 4, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 216 216, g32p_row02_traceSegment_046_0000_0216, g32p_row02_traceSegment_046_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 432 13 14, g32p_row02_traceSegment_046_0432_0013, g32p_row02_traceSegment_046_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 459 13 14, g32p_row02_traceSegment_046_0459_0013, g32p_row02_traceSegment_046_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 432 27 27, g32p_row02_traceSegment_046_0432_0027, g32p_row02_traceSegment_046_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 486 13 14, g32p_row02_traceSegment_046_0486_0013, g32p_row02_traceSegment_046_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 526 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 513 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 513 13 14, g32p_row02_traceSegment_046_0513_0013, g32p_row02_traceSegment_046_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 486 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 486 27 27, g32p_row02_traceSegment_046_0486_0027, g32p_row02_traceSegment_046_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 432 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 432 54 54, g32p_row02_traceSegment_046_0432_0054, g32p_row02_traceSegment_046_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 540 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 553 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 540 27 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 540 13 14, g32p_row02_traceSegment_046_0540_0013, g32p_row02_traceSegment_046_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 567 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 580 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 567 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 567 13 14, g32p_row02_traceSegment_046_0567_0013, g32p_row02_traceSegment_046_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 540 54 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 540 27 27, g32p_row02_traceSegment_046_0540_0027, g32p_row02_traceSegment_046_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 594 13 14, g32p_row02_traceSegment_046_0594_0013, g32p_row02_traceSegment_046_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 621 13 14, g32p_row02_traceSegment_046_0621_0013, g32p_row02_traceSegment_046_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 594 27 27, g32p_row02_traceSegment_046_0594_0027, g32p_row02_traceSegment_046_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 540 108 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 540 54 54, g32p_row02_traceSegment_046_0540_0054, g32p_row02_traceSegment_046_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 432 216 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 432 108 108, g32p_row02_traceSegment_046_0432_0108, g32p_row02_traceSegment_046_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 648 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 661 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 648 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 648 13 14, g32p_row02_traceSegment_046_0648_0013, g32p_row02_traceSegment_046_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 675 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 688 14 = [0, 1, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 675 27 = [0, 2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 675 13 14, g32p_row02_traceSegment_046_0675_0013, g32p_row02_traceSegment_046_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 648 54 = [0, 4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 648 27 27, g32p_row02_traceSegment_046_0648_0027, g32p_row02_traceSegment_046_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 702 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 715 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 702 27 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 702 13 14, g32p_row02_traceSegment_046_0702_0013, g32p_row02_traceSegment_046_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 729 13 = [0, 1, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 742 14 = [0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 729 27 = [0, 2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 729 13 14, g32p_row02_traceSegment_046_0729_0013, g32p_row02_traceSegment_046_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 702 54 = [0, 2, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 702 27 27, g32p_row02_traceSegment_046_0702_0027, g32p_row02_traceSegment_046_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 648 108 = [0, 6, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 648 54 54, g32p_row02_traceSegment_046_0648_0054, g32p_row02_traceSegment_046_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 756 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 769 14 = [0, 2, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 756 27 = [0, 2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 756 13 14, g32p_row02_traceSegment_046_0756_0013, g32p_row02_traceSegment_046_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 783 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 796 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 783 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 783 13 14, g32p_row02_traceSegment_046_0783_0013, g32p_row02_traceSegment_046_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 756 54 = [0, 2, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 756 27 27, g32p_row02_traceSegment_046_0756_0027, g32p_row02_traceSegment_046_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 810 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 823 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 810 27 = [0, 2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 810 13 14, g32p_row02_traceSegment_046_0810_0013, g32p_row02_traceSegment_046_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 837 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 837 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 837 13 14, g32p_row02_traceSegment_046_0837_0013, g32p_row02_traceSegment_046_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 810 54 = [0, 2, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 810 27 27, g32p_row02_traceSegment_046_0810_0027, g32p_row02_traceSegment_046_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 756 108 = [0, 4, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 756 54 54, g32p_row02_traceSegment_046_0756_0054, g32p_row02_traceSegment_046_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 648 216 = [0, 10, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 648 108 108, g32p_row02_traceSegment_046_0648_0108, g32p_row02_traceSegment_046_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 432 432 = [0, 10, 0, 38] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 432 216 216, g32p_row02_traceSegment_046_0432_0216, g32p_row02_traceSegment_046_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_046 0 864 = [0, 14, 0, 44] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 432 432, g32p_row02_traceSegment_046_0000_0432, g32p_row02_traceSegment_046_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 864 13 14, g32p_row02_traceSegment_046_0864_0013, g32p_row02_traceSegment_046_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 891 13 14, g32p_row02_traceSegment_046_0891_0013, g32p_row02_traceSegment_046_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 864 27 27, g32p_row02_traceSegment_046_0864_0027, g32p_row02_traceSegment_046_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 931 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 918 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 918 13 14, g32p_row02_traceSegment_046_0918_0013, g32p_row02_traceSegment_046_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 945 13 = [0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 958 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 945 27 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 945 13 14, g32p_row02_traceSegment_046_0945_0013, g32p_row02_traceSegment_046_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 918 54 = [0, 3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 918 27 27, g32p_row02_traceSegment_046_0918_0027, g32p_row02_traceSegment_046_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 864 108 = [0, 3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 864 54 54, g32p_row02_traceSegment_046_0864_0054, g32p_row02_traceSegment_046_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 985 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 972 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 972 13 14, g32p_row02_traceSegment_046_0972_0013, g32p_row02_traceSegment_046_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 999 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1012 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 999 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 999 13 14, g32p_row02_traceSegment_046_0999_0013, g32p_row02_traceSegment_046_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 972 54 = [0, 1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 972 27 27, g32p_row02_traceSegment_046_0972_0027, g32p_row02_traceSegment_046_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1026 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1026 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1026 13 14, g32p_row02_traceSegment_046_1026_0013, g32p_row02_traceSegment_046_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1053 13 14, g32p_row02_traceSegment_046_1053_0013, g32p_row02_traceSegment_046_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1026 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1026 27 27, g32p_row02_traceSegment_046_1026_0027, g32p_row02_traceSegment_046_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 972 108 = [0, 1, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 972 54 54, g32p_row02_traceSegment_046_0972_0054, g32p_row02_traceSegment_046_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 864 216 = [0, 4, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 864 108 108, g32p_row02_traceSegment_046_0864_0108, g32p_row02_traceSegment_046_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1080 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1093 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1080 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1080 13 14, g32p_row02_traceSegment_046_1080_0013, g32p_row02_traceSegment_046_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1107 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1120 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1107 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1107 13 14, g32p_row02_traceSegment_046_1107_0013, g32p_row02_traceSegment_046_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1080 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1080 27 27, g32p_row02_traceSegment_046_1080_0027, g32p_row02_traceSegment_046_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1134 13 14, g32p_row02_traceSegment_046_1134_0013, g32p_row02_traceSegment_046_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1161 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1174 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1161 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1161 13 14, g32p_row02_traceSegment_046_1161_0013, g32p_row02_traceSegment_046_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1134 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1134 27 27, g32p_row02_traceSegment_046_1134_0027, g32p_row02_traceSegment_046_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1080 108 = [0, 3, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1080 54 54, g32p_row02_traceSegment_046_1080_0054, g32p_row02_traceSegment_046_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1188 13 14, g32p_row02_traceSegment_046_1188_0013, g32p_row02_traceSegment_046_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1215 13 14, g32p_row02_traceSegment_046_1215_0013, g32p_row02_traceSegment_046_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1188 27 27, g32p_row02_traceSegment_046_1188_0027, g32p_row02_traceSegment_046_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1255 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1242 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1242 13 14, g32p_row02_traceSegment_046_1242_0013, g32p_row02_traceSegment_046_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1269 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1282 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1269 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1269 13 14, g32p_row02_traceSegment_046_1269_0013, g32p_row02_traceSegment_046_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1242 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1242 27 27, g32p_row02_traceSegment_046_1242_0027, g32p_row02_traceSegment_046_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1188 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1188 54 54, g32p_row02_traceSegment_046_1188_0054, g32p_row02_traceSegment_046_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 1080 216 = [0, 6, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1080 108 108, g32p_row02_traceSegment_046_1080_0108, g32p_row02_traceSegment_046_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 864 432 = [0, 10, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 864 216 216, g32p_row02_traceSegment_046_0864_0216, g32p_row02_traceSegment_046_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1296 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1296 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1296 13 14, g32p_row02_traceSegment_046_1296_0013, g32p_row02_traceSegment_046_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1336 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1323 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1323 13 14, g32p_row02_traceSegment_046_1323_0013, g32p_row02_traceSegment_046_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1296 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1296 27 27, g32p_row02_traceSegment_046_1296_0027, g32p_row02_traceSegment_046_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1350 13 14, g32p_row02_traceSegment_046_1350_0013, g32p_row02_traceSegment_046_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1377 13 14, g32p_row02_traceSegment_046_1377_0013, g32p_row02_traceSegment_046_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1350 27 27, g32p_row02_traceSegment_046_1350_0027, g32p_row02_traceSegment_046_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1296 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1296 54 54, g32p_row02_traceSegment_046_1296_0054, g32p_row02_traceSegment_046_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1404 13 14, g32p_row02_traceSegment_046_1404_0013, g32p_row02_traceSegment_046_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1444 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1431 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1431 13 14, g32p_row02_traceSegment_046_1431_0013, g32p_row02_traceSegment_046_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1404 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1404 27 27, g32p_row02_traceSegment_046_1404_0027, g32p_row02_traceSegment_046_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1458 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1458 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1458 13 14, g32p_row02_traceSegment_046_1458_0013, g32p_row02_traceSegment_046_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1498 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1485 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1485 13 14, g32p_row02_traceSegment_046_1485_0013, g32p_row02_traceSegment_046_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1458 54 = [0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1458 27 27, g32p_row02_traceSegment_046_1458_0027, g32p_row02_traceSegment_046_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1404 108 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1404 54 54, g32p_row02_traceSegment_046_1404_0054, g32p_row02_traceSegment_046_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 1296 216 = [0, 1, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1296 108 108, g32p_row02_traceSegment_046_1296_0108, g32p_row02_traceSegment_046_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1512 13 14, g32p_row02_traceSegment_046_1512_0013, g32p_row02_traceSegment_046_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1539 13 14, g32p_row02_traceSegment_046_1539_0013, g32p_row02_traceSegment_046_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1512 27 27, g32p_row02_traceSegment_046_1512_0027, g32p_row02_traceSegment_046_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1566 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1566 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1566 13 14, g32p_row02_traceSegment_046_1566_0013, g32p_row02_traceSegment_046_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1606 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1593 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1593 13 14, g32p_row02_traceSegment_046_1593_0013, g32p_row02_traceSegment_046_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1566 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1566 27 27, g32p_row02_traceSegment_046_1566_0027, g32p_row02_traceSegment_046_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1512 108 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1512 54 54, g32p_row02_traceSegment_046_1512_0054, g32p_row02_traceSegment_046_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1620 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1633 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1620 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1620 13 14, g32p_row02_traceSegment_046_1620_0013, g32p_row02_traceSegment_046_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1647 13 14, g32p_row02_traceSegment_046_1647_0013, g32p_row02_traceSegment_046_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1620 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1620 27 27, g32p_row02_traceSegment_046_1620_0027, g32p_row02_traceSegment_046_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1674 13 14, g32p_row02_traceSegment_046_1674_0013, g32p_row02_traceSegment_046_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1701 13 14, g32p_row02_traceSegment_046_1701_0013, g32p_row02_traceSegment_046_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1674 27 27, g32p_row02_traceSegment_046_1674_0027, g32p_row02_traceSegment_046_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1620 108 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1620 54 54, g32p_row02_traceSegment_046_1620_0054, g32p_row02_traceSegment_046_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 1512 216 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1512 108 108, g32p_row02_traceSegment_046_1512_0108, g32p_row02_traceSegment_046_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 1296 432 = [0, 1, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1296 216 216, g32p_row02_traceSegment_046_1296_0216, g32p_row02_traceSegment_046_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_046 864 864 = [0, 11, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 864 432 432, g32p_row02_traceSegment_046_0864_0432, g32p_row02_traceSegment_046_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_046 0 1728 = [0, 25, 0, 68] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 864 864, g32p_row02_traceSegment_046_0000_0864, g32p_row02_traceSegment_046_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1728 13 14, g32p_row02_traceSegment_046_1728_0013, g32p_row02_traceSegment_046_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1755 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1768 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1755 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1755 13 14, g32p_row02_traceSegment_046_1755_0013, g32p_row02_traceSegment_046_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1728 27 27, g32p_row02_traceSegment_046_1728_0027, g32p_row02_traceSegment_046_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1782 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1782 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1782 13 14, g32p_row02_traceSegment_046_1782_0013, g32p_row02_traceSegment_046_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1809 13 14, g32p_row02_traceSegment_046_1809_0013, g32p_row02_traceSegment_046_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1782 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1782 27 27, g32p_row02_traceSegment_046_1782_0027, g32p_row02_traceSegment_046_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 108 = [0, 2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1728 54 54, g32p_row02_traceSegment_046_1728_0054, g32p_row02_traceSegment_046_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1836 13 14, g32p_row02_traceSegment_046_1836_0013, g32p_row02_traceSegment_046_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1876 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1863 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1863 13 14, g32p_row02_traceSegment_046_1863_0013, g32p_row02_traceSegment_046_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1836 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1836 27 27, g32p_row02_traceSegment_046_1836_0027, g32p_row02_traceSegment_046_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1890 13 14, g32p_row02_traceSegment_046_1890_0013, g32p_row02_traceSegment_046_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1917 13 14, g32p_row02_traceSegment_046_1917_0013, g32p_row02_traceSegment_046_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1890 27 27, g32p_row02_traceSegment_046_1890_0027, g32p_row02_traceSegment_046_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1836 108 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1836 54 54, g32p_row02_traceSegment_046_1836_0054, g32p_row02_traceSegment_046_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 216 = [0, 2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1728 108 108, g32p_row02_traceSegment_046_1728_0108, g32p_row02_traceSegment_046_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1944 13 14, g32p_row02_traceSegment_046_1944_0013, g32p_row02_traceSegment_046_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1971 13 14, g32p_row02_traceSegment_046_1971_0013, g32p_row02_traceSegment_046_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1944 27 27, g32p_row02_traceSegment_046_1944_0027, g32p_row02_traceSegment_046_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1998 13 14, g32p_row02_traceSegment_046_1998_0013, g32p_row02_traceSegment_046_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2025 13 14, g32p_row02_traceSegment_046_2025_0013, g32p_row02_traceSegment_046_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1998 27 27, g32p_row02_traceSegment_046_1998_0027, g32p_row02_traceSegment_046_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1944 54 54, g32p_row02_traceSegment_046_1944_0054, g32p_row02_traceSegment_046_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2052 13 14, g32p_row02_traceSegment_046_2052_0013, g32p_row02_traceSegment_046_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2079 13 14, g32p_row02_traceSegment_046_2079_0013, g32p_row02_traceSegment_046_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2052 27 27, g32p_row02_traceSegment_046_2052_0027, g32p_row02_traceSegment_046_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2106 13 14, g32p_row02_traceSegment_046_2106_0013, g32p_row02_traceSegment_046_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2133 13 14, g32p_row02_traceSegment_046_2133_0013, g32p_row02_traceSegment_046_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2106 27 27, g32p_row02_traceSegment_046_2106_0027, g32p_row02_traceSegment_046_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2052 54 54, g32p_row02_traceSegment_046_2052_0054, g32p_row02_traceSegment_046_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1944 108 108, g32p_row02_traceSegment_046_1944_0108, g32p_row02_traceSegment_046_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 432 = [0, 2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1728 216 216, g32p_row02_traceSegment_046_1728_0216, g32p_row02_traceSegment_046_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2160 13 14, g32p_row02_traceSegment_046_2160_0013, g32p_row02_traceSegment_046_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2187 13 14, g32p_row02_traceSegment_046_2187_0013, g32p_row02_traceSegment_046_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2160 27 27, g32p_row02_traceSegment_046_2160_0027, g32p_row02_traceSegment_046_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2214 13 14, g32p_row02_traceSegment_046_2214_0013, g32p_row02_traceSegment_046_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2241 13 14, g32p_row02_traceSegment_046_2241_0013, g32p_row02_traceSegment_046_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2214 27 27, g32p_row02_traceSegment_046_2214_0027, g32p_row02_traceSegment_046_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2160 54 54, g32p_row02_traceSegment_046_2160_0054, g32p_row02_traceSegment_046_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2268 13 14, g32p_row02_traceSegment_046_2268_0013, g32p_row02_traceSegment_046_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2295 13 14, g32p_row02_traceSegment_046_2295_0013, g32p_row02_traceSegment_046_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2268 27 27, g32p_row02_traceSegment_046_2268_0027, g32p_row02_traceSegment_046_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2322 13 14, g32p_row02_traceSegment_046_2322_0013, g32p_row02_traceSegment_046_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2349 13 14, g32p_row02_traceSegment_046_2349_0013, g32p_row02_traceSegment_046_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2322 27 27, g32p_row02_traceSegment_046_2322_0027, g32p_row02_traceSegment_046_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2268 54 54, g32p_row02_traceSegment_046_2268_0054, g32p_row02_traceSegment_046_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2160 108 108, g32p_row02_traceSegment_046_2160_0108, g32p_row02_traceSegment_046_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2376 13 14, g32p_row02_traceSegment_046_2376_0013, g32p_row02_traceSegment_046_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2403 13 14, g32p_row02_traceSegment_046_2403_0013, g32p_row02_traceSegment_046_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2376 27 27, g32p_row02_traceSegment_046_2376_0027, g32p_row02_traceSegment_046_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2430 13 14, g32p_row02_traceSegment_046_2430_0013, g32p_row02_traceSegment_046_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2457 13 14, g32p_row02_traceSegment_046_2457_0013, g32p_row02_traceSegment_046_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2430 27 27, g32p_row02_traceSegment_046_2430_0027, g32p_row02_traceSegment_046_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2376 54 54, g32p_row02_traceSegment_046_2376_0054, g32p_row02_traceSegment_046_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2484 13 14, g32p_row02_traceSegment_046_2484_0013, g32p_row02_traceSegment_046_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2524 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2511 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2511 13 14, g32p_row02_traceSegment_046_2511_0013, g32p_row02_traceSegment_046_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2484 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2484 27 27, g32p_row02_traceSegment_046_2484_0027, g32p_row02_traceSegment_046_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2538 13 14, g32p_row02_traceSegment_046_2538_0013, g32p_row02_traceSegment_046_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2565 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2565 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2565 13 14, g32p_row02_traceSegment_046_2565_0013, g32p_row02_traceSegment_046_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2538 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2538 27 27, g32p_row02_traceSegment_046_2538_0027, g32p_row02_traceSegment_046_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2484 108 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2484 54 54, g32p_row02_traceSegment_046_2484_0054, g32p_row02_traceSegment_046_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 2376 216 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2376 108 108, g32p_row02_traceSegment_046_2376_0108, g32p_row02_traceSegment_046_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 2160 432 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2160 216 216, g32p_row02_traceSegment_046_2160_0216, g32p_row02_traceSegment_046_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 864 = [0, 3, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1728 432 432, g32p_row02_traceSegment_046_1728_0432, g32p_row02_traceSegment_046_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2592 13 14, g32p_row02_traceSegment_046_2592_0013, g32p_row02_traceSegment_046_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2632 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2619 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2619 13 14, g32p_row02_traceSegment_046_2619_0013, g32p_row02_traceSegment_046_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2592 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2592 27 27, g32p_row02_traceSegment_046_2592_0027, g32p_row02_traceSegment_046_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2646 13 14, g32p_row02_traceSegment_046_2646_0013, g32p_row02_traceSegment_046_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2673 13 14, g32p_row02_traceSegment_046_2673_0013, g32p_row02_traceSegment_046_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2646 27 27, g32p_row02_traceSegment_046_2646_0027, g32p_row02_traceSegment_046_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2592 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2592 54 54, g32p_row02_traceSegment_046_2592_0054, g32p_row02_traceSegment_046_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2700 13 14, g32p_row02_traceSegment_046_2700_0013, g32p_row02_traceSegment_046_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2727 13 14, g32p_row02_traceSegment_046_2727_0013, g32p_row02_traceSegment_046_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2700 27 27, g32p_row02_traceSegment_046_2700_0027, g32p_row02_traceSegment_046_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2754 13 14, g32p_row02_traceSegment_046_2754_0013, g32p_row02_traceSegment_046_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2781 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2781 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2781 13 14, g32p_row02_traceSegment_046_2781_0013, g32p_row02_traceSegment_046_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2754 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2754 27 27, g32p_row02_traceSegment_046_2754_0027, g32p_row02_traceSegment_046_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2700 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2700 54 54, g32p_row02_traceSegment_046_2700_0054, g32p_row02_traceSegment_046_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 2592 216 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2592 108 108, g32p_row02_traceSegment_046_2592_0108, g32p_row02_traceSegment_046_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2808 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2821 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2808 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2808 13 14, g32p_row02_traceSegment_046_2808_0013, g32p_row02_traceSegment_046_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2835 13 = [0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2835 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2835 13 14, g32p_row02_traceSegment_046_2835_0013, g32p_row02_traceSegment_046_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2808 54 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2808 27 27, g32p_row02_traceSegment_046_2808_0027, g32p_row02_traceSegment_046_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2862 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2875 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2862 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2862 13 14, g32p_row02_traceSegment_046_2862_0013, g32p_row02_traceSegment_046_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2902 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2889 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2889 13 14, g32p_row02_traceSegment_046_2889_0013, g32p_row02_traceSegment_046_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2862 54 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2862 27 27, g32p_row02_traceSegment_046_2862_0027, g32p_row02_traceSegment_046_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2808 108 = [0, 1, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2808 54 54, g32p_row02_traceSegment_046_2808_0054, g32p_row02_traceSegment_046_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2916 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2929 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2916 27 = [0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2916 13 14, g32p_row02_traceSegment_046_2916_0013, g32p_row02_traceSegment_046_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2943 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2943 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2943 13 14, g32p_row02_traceSegment_046_2943_0013, g32p_row02_traceSegment_046_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2916 54 = [0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2916 27 27, g32p_row02_traceSegment_046_2916_0027, g32p_row02_traceSegment_046_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 2983 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2970 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2970 13 14, g32p_row02_traceSegment_046_2970_0013, g32p_row02_traceSegment_046_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2997 13 14, g32p_row02_traceSegment_046_2997_0013, g32p_row02_traceSegment_046_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 2970 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2970 27 27, g32p_row02_traceSegment_046_2970_0027, g32p_row02_traceSegment_046_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 2916 108 = [0, 1, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2916 54 54, g32p_row02_traceSegment_046_2916_0054, g32p_row02_traceSegment_046_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 2808 216 = [0, 2, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2808 108 108, g32p_row02_traceSegment_046_2808_0108, g32p_row02_traceSegment_046_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 2592 432 = [0, 2, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2592 216 216, g32p_row02_traceSegment_046_2592_0216, g32p_row02_traceSegment_046_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3024 13 14, g32p_row02_traceSegment_046_3024_0013, g32p_row02_traceSegment_046_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3064 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3051 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3051 13 14, g32p_row02_traceSegment_046_3051_0013, g32p_row02_traceSegment_046_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3024 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3024 27 27, g32p_row02_traceSegment_046_3024_0027, g32p_row02_traceSegment_046_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3078 13 14, g32p_row02_traceSegment_046_3078_0013, g32p_row02_traceSegment_046_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3105 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3105 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3105 13 14, g32p_row02_traceSegment_046_3105_0013, g32p_row02_traceSegment_046_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3078 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3078 27 27, g32p_row02_traceSegment_046_3078_0027, g32p_row02_traceSegment_046_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 3024 108 = [0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3024 54 54, g32p_row02_traceSegment_046_3024_0054, g32p_row02_traceSegment_046_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3132 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3145 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3132 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3132 13 14, g32p_row02_traceSegment_046_3132_0013, g32p_row02_traceSegment_046_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3159 13 14, g32p_row02_traceSegment_046_3159_0013, g32p_row02_traceSegment_046_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3132 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3132 27 27, g32p_row02_traceSegment_046_3132_0027, g32p_row02_traceSegment_046_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3199 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3186 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3186 13 14, g32p_row02_traceSegment_046_3186_0013, g32p_row02_traceSegment_046_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3213 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3226 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3213 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3213 13 14, g32p_row02_traceSegment_046_3213_0013, g32p_row02_traceSegment_046_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3186 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3186 27 27, g32p_row02_traceSegment_046_3186_0027, g32p_row02_traceSegment_046_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 3132 108 = [0, 8, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3132 54 54, g32p_row02_traceSegment_046_3132_0054, g32p_row02_traceSegment_046_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 3024 216 = [0, 10, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3024 108 108, g32p_row02_traceSegment_046_3024_0108, g32p_row02_traceSegment_046_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3240 13 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3240 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3240 13 14, g32p_row02_traceSegment_046_3240_0013, g32p_row02_traceSegment_046_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3267 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3280 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3267 27 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3267 13 14, g32p_row02_traceSegment_046_3267_0013, g32p_row02_traceSegment_046_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3240 54 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3240 27 27, g32p_row02_traceSegment_046_3240_0027, g32p_row02_traceSegment_046_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3294 13 = [0, 7] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3307 14 = [0, 7] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3294 27 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3294 13 14, g32p_row02_traceSegment_046_3294_0013, g32p_row02_traceSegment_046_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3321 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3334 14 = [0, 6] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3321 27 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3321 13 14, g32p_row02_traceSegment_046_3321_0013, g32p_row02_traceSegment_046_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3294 54 = [0, 23] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3294 27 27, g32p_row02_traceSegment_046_3294_0027, g32p_row02_traceSegment_046_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 3240 108 = [0, 34] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3240 54 54, g32p_row02_traceSegment_046_3240_0054, g32p_row02_traceSegment_046_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3348 13 = [0, 7] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3361 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3348 27 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3348 13 14, g32p_row02_traceSegment_046_3348_0013, g32p_row02_traceSegment_046_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3375 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3388 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3375 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3375 13 14, g32p_row02_traceSegment_046_3375_0013, g32p_row02_traceSegment_046_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3348 54 = [0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3348 27 27, g32p_row02_traceSegment_046_3348_0027, g32p_row02_traceSegment_046_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3402 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3415 14 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3402 27 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3402 13 14, g32p_row02_traceSegment_046_3402_0013, g32p_row02_traceSegment_046_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_046 3429 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_046 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_046_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_046 3429 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3429 13 14, g32p_row02_traceSegment_046_3429_0013, g32p_row02_traceSegment_046_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_046 3402 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3402 27 27, g32p_row02_traceSegment_046_3402_0027, g32p_row02_traceSegment_046_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_046 3348 108 = [0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3348 54 54, g32p_row02_traceSegment_046_3348_0054, g32p_row02_traceSegment_046_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_046 3240 216 = [0, 56] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3240 108 108, g32p_row02_traceSegment_046_3240_0108, g32p_row02_traceSegment_046_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_046_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_046 3024 432 = [0, 66, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 3024 216 216, g32p_row02_traceSegment_046_3024_0216, g32p_row02_traceSegment_046_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_046_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_046 2592 864 = [0, 68, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 2592 432 432, g32p_row02_traceSegment_046_2592_0432, g32p_row02_traceSegment_046_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_046_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_046 1728 1728 = [0, 71, 0, 28] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 1728 864 864, g32p_row02_traceSegment_046_1728_0864, g32p_row02_traceSegment_046_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_046_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_046 0 3456 = [0, 96, 0, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_046 0 1728 1728, g32p_row02_traceSegment_046_0000_1728, g32p_row02_traceSegment_046_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_046 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 46 = [0, 96, 0, 96] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_046_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_048 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 48 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_048_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 13 14, g32p_row02_traceSegment_048_0000_0013, g32p_row02_traceSegment_048_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 27 13 14, g32p_row02_traceSegment_048_0027_0013, g32p_row02_traceSegment_048_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 27 27, g32p_row02_traceSegment_048_0000_0027, g32p_row02_traceSegment_048_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 54 13 14, g32p_row02_traceSegment_048_0054_0013, g32p_row02_traceSegment_048_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 94 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 81 13 14, g32p_row02_traceSegment_048_0081_0013, g32p_row02_traceSegment_048_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 54 27 27, g32p_row02_traceSegment_048_0054_0027, g32p_row02_traceSegment_048_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 54 54, g32p_row02_traceSegment_048_0000_0054, g32p_row02_traceSegment_048_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 108 13 14, g32p_row02_traceSegment_048_0108_0013, g32p_row02_traceSegment_048_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 135 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 148 14 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 135 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 135 13 14, g32p_row02_traceSegment_048_0135_0013, g32p_row02_traceSegment_048_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 108 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 108 27 27, g32p_row02_traceSegment_048_0108_0027, g32p_row02_traceSegment_048_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 162 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 162 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 162 13 14, g32p_row02_traceSegment_048_0162_0013, g32p_row02_traceSegment_048_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 189 13 14, g32p_row02_traceSegment_048_0189_0013, g32p_row02_traceSegment_048_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 162 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 162 27 27, g32p_row02_traceSegment_048_0162_0027, g32p_row02_traceSegment_048_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 108 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 108 54 54, g32p_row02_traceSegment_048_0108_0054, g32p_row02_traceSegment_048_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 0 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 108 108, g32p_row02_traceSegment_048_0000_0108, g32p_row02_traceSegment_048_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 216 13 14, g32p_row02_traceSegment_048_0216_0013, g32p_row02_traceSegment_048_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 243 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 256 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 243 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 243 13 14, g32p_row02_traceSegment_048_0243_0013, g32p_row02_traceSegment_048_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 216 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 216 27 27, g32p_row02_traceSegment_048_0216_0027, g32p_row02_traceSegment_048_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 270 13 14, g32p_row02_traceSegment_048_0270_0013, g32p_row02_traceSegment_048_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 297 13 14, g32p_row02_traceSegment_048_0297_0013, g32p_row02_traceSegment_048_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 270 27 27, g32p_row02_traceSegment_048_0270_0027, g32p_row02_traceSegment_048_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 216 54 54, g32p_row02_traceSegment_048_0216_0054, g32p_row02_traceSegment_048_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 337 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 324 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 324 13 14, g32p_row02_traceSegment_048_0324_0013, g32p_row02_traceSegment_048_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 351 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 351 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 351 13 14, g32p_row02_traceSegment_048_0351_0013, g32p_row02_traceSegment_048_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 324 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 324 27 27, g32p_row02_traceSegment_048_0324_0027, g32p_row02_traceSegment_048_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 391 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 378 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 378 13 14, g32p_row02_traceSegment_048_0378_0013, g32p_row02_traceSegment_048_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 405 13 14, g32p_row02_traceSegment_048_0405_0013, g32p_row02_traceSegment_048_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 378 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 378 27 27, g32p_row02_traceSegment_048_0378_0027, g32p_row02_traceSegment_048_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 324 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 324 54 54, g32p_row02_traceSegment_048_0324_0054, g32p_row02_traceSegment_048_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 216 216 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 216 108 108, g32p_row02_traceSegment_048_0216_0108, g32p_row02_traceSegment_048_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 0 432 = [11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 216 216, g32p_row02_traceSegment_048_0000_0216, g32p_row02_traceSegment_048_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 432 13 14, g32p_row02_traceSegment_048_0432_0013, g32p_row02_traceSegment_048_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 459 13 14, g32p_row02_traceSegment_048_0459_0013, g32p_row02_traceSegment_048_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 432 27 27, g32p_row02_traceSegment_048_0432_0027, g32p_row02_traceSegment_048_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 486 13 14, g32p_row02_traceSegment_048_0486_0013, g32p_row02_traceSegment_048_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 513 13 14, g32p_row02_traceSegment_048_0513_0013, g32p_row02_traceSegment_048_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 486 27 27, g32p_row02_traceSegment_048_0486_0027, g32p_row02_traceSegment_048_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 432 54 54, g32p_row02_traceSegment_048_0432_0054, g32p_row02_traceSegment_048_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 540 13 14, g32p_row02_traceSegment_048_0540_0013, g32p_row02_traceSegment_048_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 567 13 14, g32p_row02_traceSegment_048_0567_0013, g32p_row02_traceSegment_048_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 540 27 27, g32p_row02_traceSegment_048_0540_0027, g32p_row02_traceSegment_048_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 594 13 14, g32p_row02_traceSegment_048_0594_0013, g32p_row02_traceSegment_048_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 621 13 14, g32p_row02_traceSegment_048_0621_0013, g32p_row02_traceSegment_048_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 594 27 27, g32p_row02_traceSegment_048_0594_0027, g32p_row02_traceSegment_048_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 540 54 54, g32p_row02_traceSegment_048_0540_0054, g32p_row02_traceSegment_048_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 432 108 108, g32p_row02_traceSegment_048_0432_0108, g32p_row02_traceSegment_048_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 648 13 14, g32p_row02_traceSegment_048_0648_0013, g32p_row02_traceSegment_048_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 675 13 14, g32p_row02_traceSegment_048_0675_0013, g32p_row02_traceSegment_048_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 648 27 27, g32p_row02_traceSegment_048_0648_0027, g32p_row02_traceSegment_048_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 702 13 14, g32p_row02_traceSegment_048_0702_0013, g32p_row02_traceSegment_048_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 729 13 14, g32p_row02_traceSegment_048_0729_0013, g32p_row02_traceSegment_048_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 702 27 27, g32p_row02_traceSegment_048_0702_0027, g32p_row02_traceSegment_048_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 648 54 54, g32p_row02_traceSegment_048_0648_0054, g32p_row02_traceSegment_048_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 756 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 756 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 756 13 14, g32p_row02_traceSegment_048_0756_0013, g32p_row02_traceSegment_048_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 783 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 783 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 783 13 14, g32p_row02_traceSegment_048_0783_0013, g32p_row02_traceSegment_048_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 756 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 756 27 27, g32p_row02_traceSegment_048_0756_0027, g32p_row02_traceSegment_048_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 810 13 14, g32p_row02_traceSegment_048_0810_0013, g32p_row02_traceSegment_048_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 837 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 837 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 837 13 14, g32p_row02_traceSegment_048_0837_0013, g32p_row02_traceSegment_048_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 810 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 810 27 27, g32p_row02_traceSegment_048_0810_0027, g32p_row02_traceSegment_048_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 756 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 756 54 54, g32p_row02_traceSegment_048_0756_0054, g32p_row02_traceSegment_048_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 648 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 648 108 108, g32p_row02_traceSegment_048_0648_0108, g32p_row02_traceSegment_048_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 432 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 432 216 216, g32p_row02_traceSegment_048_0432_0216, g32p_row02_traceSegment_048_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_048 0 864 = [17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 432 432, g32p_row02_traceSegment_048_0000_0432, g32p_row02_traceSegment_048_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 864 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 864 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 864 13 14, g32p_row02_traceSegment_048_0864_0013, g32p_row02_traceSegment_048_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 891 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 904 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 891 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 891 13 14, g32p_row02_traceSegment_048_0891_0013, g32p_row02_traceSegment_048_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 864 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 864 27 27, g32p_row02_traceSegment_048_0864_0027, g32p_row02_traceSegment_048_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 918 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 918 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 918 13 14, g32p_row02_traceSegment_048_0918_0013, g32p_row02_traceSegment_048_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 945 13 14, g32p_row02_traceSegment_048_0945_0013, g32p_row02_traceSegment_048_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 918 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 918 27 27, g32p_row02_traceSegment_048_0918_0027, g32p_row02_traceSegment_048_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 864 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 864 54 54, g32p_row02_traceSegment_048_0864_0054, g32p_row02_traceSegment_048_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 972 13 14, g32p_row02_traceSegment_048_0972_0013, g32p_row02_traceSegment_048_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 999 13 14, g32p_row02_traceSegment_048_0999_0013, g32p_row02_traceSegment_048_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 972 27 27, g32p_row02_traceSegment_048_0972_0027, g32p_row02_traceSegment_048_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1039 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1026 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1026 13 14, g32p_row02_traceSegment_048_1026_0013, g32p_row02_traceSegment_048_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1053 13 14, g32p_row02_traceSegment_048_1053_0013, g32p_row02_traceSegment_048_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1026 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1026 27 27, g32p_row02_traceSegment_048_1026_0027, g32p_row02_traceSegment_048_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 972 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 972 54 54, g32p_row02_traceSegment_048_0972_0054, g32p_row02_traceSegment_048_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 864 216 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 864 108 108, g32p_row02_traceSegment_048_0864_0108, g32p_row02_traceSegment_048_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1080 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1080 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1080 13 14, g32p_row02_traceSegment_048_1080_0013, g32p_row02_traceSegment_048_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1120 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1107 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1107 13 14, g32p_row02_traceSegment_048_1107_0013, g32p_row02_traceSegment_048_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1080 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1080 27 27, g32p_row02_traceSegment_048_1080_0027, g32p_row02_traceSegment_048_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1134 13 14, g32p_row02_traceSegment_048_1134_0013, g32p_row02_traceSegment_048_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1161 13 14, g32p_row02_traceSegment_048_1161_0013, g32p_row02_traceSegment_048_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1134 27 27, g32p_row02_traceSegment_048_1134_0027, g32p_row02_traceSegment_048_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1080 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1080 54 54, g32p_row02_traceSegment_048_1080_0054, g32p_row02_traceSegment_048_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1188 13 14, g32p_row02_traceSegment_048_1188_0013, g32p_row02_traceSegment_048_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1215 13 14, g32p_row02_traceSegment_048_1215_0013, g32p_row02_traceSegment_048_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1188 27 27, g32p_row02_traceSegment_048_1188_0027, g32p_row02_traceSegment_048_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1242 13 14, g32p_row02_traceSegment_048_1242_0013, g32p_row02_traceSegment_048_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1269 13 14, g32p_row02_traceSegment_048_1269_0013, g32p_row02_traceSegment_048_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1242 27 27, g32p_row02_traceSegment_048_1242_0027, g32p_row02_traceSegment_048_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1188 54 54, g32p_row02_traceSegment_048_1188_0054, g32p_row02_traceSegment_048_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 1080 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1080 108 108, g32p_row02_traceSegment_048_1080_0108, g32p_row02_traceSegment_048_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 864 432 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 864 216 216, g32p_row02_traceSegment_048_0864_0216, g32p_row02_traceSegment_048_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1296 13 14, g32p_row02_traceSegment_048_1296_0013, g32p_row02_traceSegment_048_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1323 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1323 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1323 13 14, g32p_row02_traceSegment_048_1323_0013, g32p_row02_traceSegment_048_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1296 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1296 27 27, g32p_row02_traceSegment_048_1296_0027, g32p_row02_traceSegment_048_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1350 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1363 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1350 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1350 13 14, g32p_row02_traceSegment_048_1350_0013, g32p_row02_traceSegment_048_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1377 13 14, g32p_row02_traceSegment_048_1377_0013, g32p_row02_traceSegment_048_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1350 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1350 27 27, g32p_row02_traceSegment_048_1350_0027, g32p_row02_traceSegment_048_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1296 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1296 54 54, g32p_row02_traceSegment_048_1296_0054, g32p_row02_traceSegment_048_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1404 13 14, g32p_row02_traceSegment_048_1404_0013, g32p_row02_traceSegment_048_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1431 13 14, g32p_row02_traceSegment_048_1431_0013, g32p_row02_traceSegment_048_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1404 27 27, g32p_row02_traceSegment_048_1404_0027, g32p_row02_traceSegment_048_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1458 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1458 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1458 13 14, g32p_row02_traceSegment_048_1458_0013, g32p_row02_traceSegment_048_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1485 13 14, g32p_row02_traceSegment_048_1485_0013, g32p_row02_traceSegment_048_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1458 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1458 27 27, g32p_row02_traceSegment_048_1458_0027, g32p_row02_traceSegment_048_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1404 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1404 54 54, g32p_row02_traceSegment_048_1404_0054, g32p_row02_traceSegment_048_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 1296 216 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1296 108 108, g32p_row02_traceSegment_048_1296_0108, g32p_row02_traceSegment_048_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1525 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1512 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1512 13 14, g32p_row02_traceSegment_048_1512_0013, g32p_row02_traceSegment_048_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1539 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1552 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1539 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1539 13 14, g32p_row02_traceSegment_048_1539_0013, g32p_row02_traceSegment_048_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1512 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1512 27 27, g32p_row02_traceSegment_048_1512_0027, g32p_row02_traceSegment_048_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1566 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1579 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1566 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1566 13 14, g32p_row02_traceSegment_048_1566_0013, g32p_row02_traceSegment_048_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1593 13 14, g32p_row02_traceSegment_048_1593_0013, g32p_row02_traceSegment_048_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1566 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1566 27 27, g32p_row02_traceSegment_048_1566_0027, g32p_row02_traceSegment_048_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1512 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1512 54 54, g32p_row02_traceSegment_048_1512_0054, g32p_row02_traceSegment_048_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1620 13 14, g32p_row02_traceSegment_048_1620_0013, g32p_row02_traceSegment_048_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1647 13 14, g32p_row02_traceSegment_048_1647_0013, g32p_row02_traceSegment_048_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1620 27 27, g32p_row02_traceSegment_048_1620_0027, g32p_row02_traceSegment_048_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1674 13 14, g32p_row02_traceSegment_048_1674_0013, g32p_row02_traceSegment_048_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1701 13 14, g32p_row02_traceSegment_048_1701_0013, g32p_row02_traceSegment_048_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1674 27 27, g32p_row02_traceSegment_048_1674_0027, g32p_row02_traceSegment_048_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1620 54 54, g32p_row02_traceSegment_048_1620_0054, g32p_row02_traceSegment_048_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 1512 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1512 108 108, g32p_row02_traceSegment_048_1512_0108, g32p_row02_traceSegment_048_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 1296 432 = [11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1296 216 216, g32p_row02_traceSegment_048_1296_0216, g32p_row02_traceSegment_048_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_048 864 864 = [21] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 864 432 432, g32p_row02_traceSegment_048_0864_0432, g32p_row02_traceSegment_048_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_048 0 1728 = [38] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 864 864, g32p_row02_traceSegment_048_0000_0864, g32p_row02_traceSegment_048_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1728 13 14, g32p_row02_traceSegment_048_1728_0013, g32p_row02_traceSegment_048_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1755 13 14, g32p_row02_traceSegment_048_1755_0013, g32p_row02_traceSegment_048_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1728 27 27, g32p_row02_traceSegment_048_1728_0027, g32p_row02_traceSegment_048_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1782 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1782 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1782 13 14, g32p_row02_traceSegment_048_1782_0013, g32p_row02_traceSegment_048_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1809 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1809 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1809 13 14, g32p_row02_traceSegment_048_1809_0013, g32p_row02_traceSegment_048_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1782 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1782 27 27, g32p_row02_traceSegment_048_1782_0027, g32p_row02_traceSegment_048_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1728 54 54, g32p_row02_traceSegment_048_1728_0054, g32p_row02_traceSegment_048_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1836 13 14, g32p_row02_traceSegment_048_1836_0013, g32p_row02_traceSegment_048_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1876 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1863 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1863 13 14, g32p_row02_traceSegment_048_1863_0013, g32p_row02_traceSegment_048_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1836 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1836 27 27, g32p_row02_traceSegment_048_1836_0027, g32p_row02_traceSegment_048_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1890 13 14, g32p_row02_traceSegment_048_1890_0013, g32p_row02_traceSegment_048_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1930 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1917 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1917 13 14, g32p_row02_traceSegment_048_1917_0013, g32p_row02_traceSegment_048_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1890 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1890 27 27, g32p_row02_traceSegment_048_1890_0027, g32p_row02_traceSegment_048_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1836 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1836 54 54, g32p_row02_traceSegment_048_1836_0054, g32p_row02_traceSegment_048_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1728 108 108, g32p_row02_traceSegment_048_1728_0108, g32p_row02_traceSegment_048_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1944 13 14, g32p_row02_traceSegment_048_1944_0013, g32p_row02_traceSegment_048_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 1984 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1971 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1971 13 14, g32p_row02_traceSegment_048_1971_0013, g32p_row02_traceSegment_048_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1944 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1944 27 27, g32p_row02_traceSegment_048_1944_0027, g32p_row02_traceSegment_048_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1998 13 14, g32p_row02_traceSegment_048_1998_0013, g32p_row02_traceSegment_048_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2025 13 14, g32p_row02_traceSegment_048_2025_0013, g32p_row02_traceSegment_048_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1998 27 27, g32p_row02_traceSegment_048_1998_0027, g32p_row02_traceSegment_048_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 1944 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1944 54 54, g32p_row02_traceSegment_048_1944_0054, g32p_row02_traceSegment_048_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2052 13 14, g32p_row02_traceSegment_048_2052_0013, g32p_row02_traceSegment_048_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2079 13 14, g32p_row02_traceSegment_048_2079_0013, g32p_row02_traceSegment_048_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2052 27 27, g32p_row02_traceSegment_048_2052_0027, g32p_row02_traceSegment_048_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2106 13 14, g32p_row02_traceSegment_048_2106_0013, g32p_row02_traceSegment_048_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2133 13 14, g32p_row02_traceSegment_048_2133_0013, g32p_row02_traceSegment_048_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2106 27 27, g32p_row02_traceSegment_048_2106_0027, g32p_row02_traceSegment_048_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2052 54 54, g32p_row02_traceSegment_048_2052_0054, g32p_row02_traceSegment_048_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 1944 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1944 108 108, g32p_row02_traceSegment_048_1944_0108, g32p_row02_traceSegment_048_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 432 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1728 216 216, g32p_row02_traceSegment_048_1728_0216, g32p_row02_traceSegment_048_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2160 13 14, g32p_row02_traceSegment_048_2160_0013, g32p_row02_traceSegment_048_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2187 13 14, g32p_row02_traceSegment_048_2187_0013, g32p_row02_traceSegment_048_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2160 27 27, g32p_row02_traceSegment_048_2160_0027, g32p_row02_traceSegment_048_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2214 13 14, g32p_row02_traceSegment_048_2214_0013, g32p_row02_traceSegment_048_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2241 13 14, g32p_row02_traceSegment_048_2241_0013, g32p_row02_traceSegment_048_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2214 27 27, g32p_row02_traceSegment_048_2214_0027, g32p_row02_traceSegment_048_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2160 54 54, g32p_row02_traceSegment_048_2160_0054, g32p_row02_traceSegment_048_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2268 13 14, g32p_row02_traceSegment_048_2268_0013, g32p_row02_traceSegment_048_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2295 13 14, g32p_row02_traceSegment_048_2295_0013, g32p_row02_traceSegment_048_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2268 27 27, g32p_row02_traceSegment_048_2268_0027, g32p_row02_traceSegment_048_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2322 13 14, g32p_row02_traceSegment_048_2322_0013, g32p_row02_traceSegment_048_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2349 13 14, g32p_row02_traceSegment_048_2349_0013, g32p_row02_traceSegment_048_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2322 27 27, g32p_row02_traceSegment_048_2322_0027, g32p_row02_traceSegment_048_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2268 54 54, g32p_row02_traceSegment_048_2268_0054, g32p_row02_traceSegment_048_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2160 108 108, g32p_row02_traceSegment_048_2160_0108, g32p_row02_traceSegment_048_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2376 13 14, g32p_row02_traceSegment_048_2376_0013, g32p_row02_traceSegment_048_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2403 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2403 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2403 13 14, g32p_row02_traceSegment_048_2403_0013, g32p_row02_traceSegment_048_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2376 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2376 27 27, g32p_row02_traceSegment_048_2376_0027, g32p_row02_traceSegment_048_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2430 13 14, g32p_row02_traceSegment_048_2430_0013, g32p_row02_traceSegment_048_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2470 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2457 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2457 13 14, g32p_row02_traceSegment_048_2457_0013, g32p_row02_traceSegment_048_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2430 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2430 27 27, g32p_row02_traceSegment_048_2430_0027, g32p_row02_traceSegment_048_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2376 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2376 54 54, g32p_row02_traceSegment_048_2376_0054, g32p_row02_traceSegment_048_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2484 13 14, g32p_row02_traceSegment_048_2484_0013, g32p_row02_traceSegment_048_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2511 13 14, g32p_row02_traceSegment_048_2511_0013, g32p_row02_traceSegment_048_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2484 27 27, g32p_row02_traceSegment_048_2484_0027, g32p_row02_traceSegment_048_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2538 13 14, g32p_row02_traceSegment_048_2538_0013, g32p_row02_traceSegment_048_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2565 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2565 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2565 13 14, g32p_row02_traceSegment_048_2565_0013, g32p_row02_traceSegment_048_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2538 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2538 27 27, g32p_row02_traceSegment_048_2538_0027, g32p_row02_traceSegment_048_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2484 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2484 54 54, g32p_row02_traceSegment_048_2484_0054, g32p_row02_traceSegment_048_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 2376 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2376 108 108, g32p_row02_traceSegment_048_2376_0108, g32p_row02_traceSegment_048_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 2160 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2160 216 216, g32p_row02_traceSegment_048_2160_0216, g32p_row02_traceSegment_048_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 864 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1728 432 432, g32p_row02_traceSegment_048_1728_0432, g32p_row02_traceSegment_048_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2592 13 14, g32p_row02_traceSegment_048_2592_0013, g32p_row02_traceSegment_048_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2619 13 14, g32p_row02_traceSegment_048_2619_0013, g32p_row02_traceSegment_048_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2592 27 27, g32p_row02_traceSegment_048_2592_0027, g32p_row02_traceSegment_048_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2659 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2646 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2646 13 14, g32p_row02_traceSegment_048_2646_0013, g32p_row02_traceSegment_048_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2673 13 14, g32p_row02_traceSegment_048_2673_0013, g32p_row02_traceSegment_048_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2646 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2646 27 27, g32p_row02_traceSegment_048_2646_0027, g32p_row02_traceSegment_048_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2592 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2592 54 54, g32p_row02_traceSegment_048_2592_0054, g32p_row02_traceSegment_048_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2700 13 14, g32p_row02_traceSegment_048_2700_0013, g32p_row02_traceSegment_048_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2727 13 14, g32p_row02_traceSegment_048_2727_0013, g32p_row02_traceSegment_048_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2700 27 27, g32p_row02_traceSegment_048_2700_0027, g32p_row02_traceSegment_048_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2754 13 14, g32p_row02_traceSegment_048_2754_0013, g32p_row02_traceSegment_048_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2781 13 14, g32p_row02_traceSegment_048_2781_0013, g32p_row02_traceSegment_048_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2754 27 27, g32p_row02_traceSegment_048_2754_0027, g32p_row02_traceSegment_048_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2700 54 54, g32p_row02_traceSegment_048_2700_0054, g32p_row02_traceSegment_048_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 2592 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2592 108 108, g32p_row02_traceSegment_048_2592_0108, g32p_row02_traceSegment_048_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2808 13 14, g32p_row02_traceSegment_048_2808_0013, g32p_row02_traceSegment_048_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2835 13 14, g32p_row02_traceSegment_048_2835_0013, g32p_row02_traceSegment_048_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2808 27 27, g32p_row02_traceSegment_048_2808_0027, g32p_row02_traceSegment_048_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2862 13 14, g32p_row02_traceSegment_048_2862_0013, g32p_row02_traceSegment_048_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2889 13 14, g32p_row02_traceSegment_048_2889_0013, g32p_row02_traceSegment_048_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2862 27 27, g32p_row02_traceSegment_048_2862_0027, g32p_row02_traceSegment_048_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2808 54 54, g32p_row02_traceSegment_048_2808_0054, g32p_row02_traceSegment_048_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2916 13 14, g32p_row02_traceSegment_048_2916_0013, g32p_row02_traceSegment_048_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2943 13 14, g32p_row02_traceSegment_048_2943_0013, g32p_row02_traceSegment_048_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2916 27 27, g32p_row02_traceSegment_048_2916_0027, g32p_row02_traceSegment_048_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2970 13 14, g32p_row02_traceSegment_048_2970_0013, g32p_row02_traceSegment_048_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2997 13 14, g32p_row02_traceSegment_048_2997_0013, g32p_row02_traceSegment_048_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2970 27 27, g32p_row02_traceSegment_048_2970_0027, g32p_row02_traceSegment_048_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2916 54 54, g32p_row02_traceSegment_048_2916_0054, g32p_row02_traceSegment_048_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2808 108 108, g32p_row02_traceSegment_048_2808_0108, g32p_row02_traceSegment_048_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 2592 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2592 216 216, g32p_row02_traceSegment_048_2592_0216, g32p_row02_traceSegment_048_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3024 13 14, g32p_row02_traceSegment_048_3024_0013, g32p_row02_traceSegment_048_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3051 13 14, g32p_row02_traceSegment_048_3051_0013, g32p_row02_traceSegment_048_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3024 27 27, g32p_row02_traceSegment_048_3024_0027, g32p_row02_traceSegment_048_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3078 13 14, g32p_row02_traceSegment_048_3078_0013, g32p_row02_traceSegment_048_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3105 13 14, g32p_row02_traceSegment_048_3105_0013, g32p_row02_traceSegment_048_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3078 27 27, g32p_row02_traceSegment_048_3078_0027, g32p_row02_traceSegment_048_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3024 54 54, g32p_row02_traceSegment_048_3024_0054, g32p_row02_traceSegment_048_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3132 13 14, g32p_row02_traceSegment_048_3132_0013, g32p_row02_traceSegment_048_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3159 13 14, g32p_row02_traceSegment_048_3159_0013, g32p_row02_traceSegment_048_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3132 27 27, g32p_row02_traceSegment_048_3132_0027, g32p_row02_traceSegment_048_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3186 13 14, g32p_row02_traceSegment_048_3186_0013, g32p_row02_traceSegment_048_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3213 13 14, g32p_row02_traceSegment_048_3213_0013, g32p_row02_traceSegment_048_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3186 27 27, g32p_row02_traceSegment_048_3186_0027, g32p_row02_traceSegment_048_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3132 54 54, g32p_row02_traceSegment_048_3132_0054, g32p_row02_traceSegment_048_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3024 108 108, g32p_row02_traceSegment_048_3024_0108, g32p_row02_traceSegment_048_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3240 13 14, g32p_row02_traceSegment_048_3240_0013, g32p_row02_traceSegment_048_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3267 13 14, g32p_row02_traceSegment_048_3267_0013, g32p_row02_traceSegment_048_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3240 27 27, g32p_row02_traceSegment_048_3240_0027, g32p_row02_traceSegment_048_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3294 13 14, g32p_row02_traceSegment_048_3294_0013, g32p_row02_traceSegment_048_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3321 13 14, g32p_row02_traceSegment_048_3321_0013, g32p_row02_traceSegment_048_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3294 27 27, g32p_row02_traceSegment_048_3294_0027, g32p_row02_traceSegment_048_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3240 54 54, g32p_row02_traceSegment_048_3240_0054, g32p_row02_traceSegment_048_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3348 13 14, g32p_row02_traceSegment_048_3348_0013, g32p_row02_traceSegment_048_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3375 13 14, g32p_row02_traceSegment_048_3375_0013, g32p_row02_traceSegment_048_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3348 27 27, g32p_row02_traceSegment_048_3348_0027, g32p_row02_traceSegment_048_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3415 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3402 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3402 13 14, g32p_row02_traceSegment_048_3402_0013, g32p_row02_traceSegment_048_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_048 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_048 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_048_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_048 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3429 13 14, g32p_row02_traceSegment_048_3429_0013, g32p_row02_traceSegment_048_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_048 3402 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3402 27 27, g32p_row02_traceSegment_048_3402_0027, g32p_row02_traceSegment_048_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_048 3348 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3348 54 54, g32p_row02_traceSegment_048_3348_0054, g32p_row02_traceSegment_048_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_048 3240 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3240 108 108, g32p_row02_traceSegment_048_3240_0108, g32p_row02_traceSegment_048_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_048_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_048 3024 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 3024 216 216, g32p_row02_traceSegment_048_3024_0216, g32p_row02_traceSegment_048_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_048_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_048 2592 864 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 2592 432 432, g32p_row02_traceSegment_048_2592_0432, g32p_row02_traceSegment_048_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_048_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_048 1728 1728 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 1728 864 864, g32p_row02_traceSegment_048_1728_0864, g32p_row02_traceSegment_048_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_048_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_048 0 3456 = [48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_048 0 1728 1728, g32p_row02_traceSegment_048_0000_1728, g32p_row02_traceSegment_048_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_048 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 48 = [48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_048_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_049 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 49 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_049_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 13 14, g32p_row02_traceSegment_049_0000_0013, g32p_row02_traceSegment_049_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 27 13 14, g32p_row02_traceSegment_049_0027_0013, g32p_row02_traceSegment_049_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 27 27, g32p_row02_traceSegment_049_0000_0027, g32p_row02_traceSegment_049_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 54 13 14, g32p_row02_traceSegment_049_0054_0013, g32p_row02_traceSegment_049_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 94 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 81 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 81 13 14, g32p_row02_traceSegment_049_0081_0013, g32p_row02_traceSegment_049_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 54 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 54 27 27, g32p_row02_traceSegment_049_0054_0027, g32p_row02_traceSegment_049_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 0 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 54 54, g32p_row02_traceSegment_049_0000_0054, g32p_row02_traceSegment_049_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 108 13 14, g32p_row02_traceSegment_049_0108_0013, g32p_row02_traceSegment_049_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 135 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 135 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 135 13 14, g32p_row02_traceSegment_049_0135_0013, g32p_row02_traceSegment_049_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 108 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 108 27 27, g32p_row02_traceSegment_049_0108_0027, g32p_row02_traceSegment_049_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 162 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 175 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 162 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 162 13 14, g32p_row02_traceSegment_049_0162_0013, g32p_row02_traceSegment_049_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 189 13 14, g32p_row02_traceSegment_049_0189_0013, g32p_row02_traceSegment_049_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 162 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 162 27 27, g32p_row02_traceSegment_049_0162_0027, g32p_row02_traceSegment_049_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 108 108 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 108 54 54, g32p_row02_traceSegment_049_0108_0054, g32p_row02_traceSegment_049_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 0 216 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 108 108, g32p_row02_traceSegment_049_0000_0108, g32p_row02_traceSegment_049_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 216 13 14, g32p_row02_traceSegment_049_0216_0013, g32p_row02_traceSegment_049_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 243 13 14, g32p_row02_traceSegment_049_0243_0013, g32p_row02_traceSegment_049_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 216 27 27, g32p_row02_traceSegment_049_0216_0027, g32p_row02_traceSegment_049_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 270 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 270 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 270 13 14, g32p_row02_traceSegment_049_0270_0013, g32p_row02_traceSegment_049_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 297 13 14, g32p_row02_traceSegment_049_0297_0013, g32p_row02_traceSegment_049_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 270 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 270 27 27, g32p_row02_traceSegment_049_0270_0027, g32p_row02_traceSegment_049_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 216 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 216 54 54, g32p_row02_traceSegment_049_0216_0054, g32p_row02_traceSegment_049_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 324 13 14, g32p_row02_traceSegment_049_0324_0013, g32p_row02_traceSegment_049_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 351 13 14, g32p_row02_traceSegment_049_0351_0013, g32p_row02_traceSegment_049_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 324 27 27, g32p_row02_traceSegment_049_0324_0027, g32p_row02_traceSegment_049_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 378 13 14, g32p_row02_traceSegment_049_0378_0013, g32p_row02_traceSegment_049_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 405 13 14, g32p_row02_traceSegment_049_0405_0013, g32p_row02_traceSegment_049_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 378 27 27, g32p_row02_traceSegment_049_0378_0027, g32p_row02_traceSegment_049_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 324 54 54, g32p_row02_traceSegment_049_0324_0054, g32p_row02_traceSegment_049_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 216 216 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 216 108 108, g32p_row02_traceSegment_049_0216_0108, g32p_row02_traceSegment_049_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 0 432 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 216 216, g32p_row02_traceSegment_049_0000_0216, g32p_row02_traceSegment_049_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 432 13 14, g32p_row02_traceSegment_049_0432_0013, g32p_row02_traceSegment_049_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 459 13 14, g32p_row02_traceSegment_049_0459_0013, g32p_row02_traceSegment_049_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 432 27 27, g32p_row02_traceSegment_049_0432_0027, g32p_row02_traceSegment_049_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 486 13 14, g32p_row02_traceSegment_049_0486_0013, g32p_row02_traceSegment_049_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 513 13 14, g32p_row02_traceSegment_049_0513_0013, g32p_row02_traceSegment_049_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 486 27 27, g32p_row02_traceSegment_049_0486_0027, g32p_row02_traceSegment_049_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 432 54 54, g32p_row02_traceSegment_049_0432_0054, g32p_row02_traceSegment_049_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 540 13 14, g32p_row02_traceSegment_049_0540_0013, g32p_row02_traceSegment_049_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 567 13 14, g32p_row02_traceSegment_049_0567_0013, g32p_row02_traceSegment_049_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 540 27 27, g32p_row02_traceSegment_049_0540_0027, g32p_row02_traceSegment_049_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 594 13 14, g32p_row02_traceSegment_049_0594_0013, g32p_row02_traceSegment_049_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 621 13 14, g32p_row02_traceSegment_049_0621_0013, g32p_row02_traceSegment_049_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 594 27 27, g32p_row02_traceSegment_049_0594_0027, g32p_row02_traceSegment_049_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 540 54 54, g32p_row02_traceSegment_049_0540_0054, g32p_row02_traceSegment_049_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 432 108 108, g32p_row02_traceSegment_049_0432_0108, g32p_row02_traceSegment_049_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 648 13 14, g32p_row02_traceSegment_049_0648_0013, g32p_row02_traceSegment_049_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 675 13 14, g32p_row02_traceSegment_049_0675_0013, g32p_row02_traceSegment_049_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 648 27 27, g32p_row02_traceSegment_049_0648_0027, g32p_row02_traceSegment_049_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 702 13 14, g32p_row02_traceSegment_049_0702_0013, g32p_row02_traceSegment_049_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 729 13 14, g32p_row02_traceSegment_049_0729_0013, g32p_row02_traceSegment_049_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 702 27 27, g32p_row02_traceSegment_049_0702_0027, g32p_row02_traceSegment_049_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 648 54 54, g32p_row02_traceSegment_049_0648_0054, g32p_row02_traceSegment_049_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 756 13 14, g32p_row02_traceSegment_049_0756_0013, g32p_row02_traceSegment_049_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 783 13 14, g32p_row02_traceSegment_049_0783_0013, g32p_row02_traceSegment_049_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 756 27 27, g32p_row02_traceSegment_049_0756_0027, g32p_row02_traceSegment_049_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 810 13 14, g32p_row02_traceSegment_049_0810_0013, g32p_row02_traceSegment_049_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 837 13 14, g32p_row02_traceSegment_049_0837_0013, g32p_row02_traceSegment_049_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 810 27 27, g32p_row02_traceSegment_049_0810_0027, g32p_row02_traceSegment_049_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 756 54 54, g32p_row02_traceSegment_049_0756_0054, g32p_row02_traceSegment_049_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 648 108 108, g32p_row02_traceSegment_049_0648_0108, g32p_row02_traceSegment_049_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 432 216 216, g32p_row02_traceSegment_049_0432_0216, g32p_row02_traceSegment_049_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_049 0 864 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 432 432, g32p_row02_traceSegment_049_0000_0432, g32p_row02_traceSegment_049_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 864 13 14, g32p_row02_traceSegment_049_0864_0013, g32p_row02_traceSegment_049_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 891 13 14, g32p_row02_traceSegment_049_0891_0013, g32p_row02_traceSegment_049_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 864 27 27, g32p_row02_traceSegment_049_0864_0027, g32p_row02_traceSegment_049_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 918 13 14, g32p_row02_traceSegment_049_0918_0013, g32p_row02_traceSegment_049_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 945 13 14, g32p_row02_traceSegment_049_0945_0013, g32p_row02_traceSegment_049_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 918 27 27, g32p_row02_traceSegment_049_0918_0027, g32p_row02_traceSegment_049_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 864 54 54, g32p_row02_traceSegment_049_0864_0054, g32p_row02_traceSegment_049_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 972 13 14, g32p_row02_traceSegment_049_0972_0013, g32p_row02_traceSegment_049_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 999 13 14, g32p_row02_traceSegment_049_0999_0013, g32p_row02_traceSegment_049_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 972 27 27, g32p_row02_traceSegment_049_0972_0027, g32p_row02_traceSegment_049_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1026 13 14, g32p_row02_traceSegment_049_1026_0013, g32p_row02_traceSegment_049_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1053 13 14, g32p_row02_traceSegment_049_1053_0013, g32p_row02_traceSegment_049_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1026 27 27, g32p_row02_traceSegment_049_1026_0027, g32p_row02_traceSegment_049_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 972 54 54, g32p_row02_traceSegment_049_0972_0054, g32p_row02_traceSegment_049_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 864 108 108, g32p_row02_traceSegment_049_0864_0108, g32p_row02_traceSegment_049_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1080 13 14, g32p_row02_traceSegment_049_1080_0013, g32p_row02_traceSegment_049_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1107 13 14, g32p_row02_traceSegment_049_1107_0013, g32p_row02_traceSegment_049_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1080 27 27, g32p_row02_traceSegment_049_1080_0027, g32p_row02_traceSegment_049_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1134 13 14, g32p_row02_traceSegment_049_1134_0013, g32p_row02_traceSegment_049_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1174 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1161 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1161 13 14, g32p_row02_traceSegment_049_1161_0013, g32p_row02_traceSegment_049_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1134 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1134 27 27, g32p_row02_traceSegment_049_1134_0027, g32p_row02_traceSegment_049_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1080 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1080 54 54, g32p_row02_traceSegment_049_1080_0054, g32p_row02_traceSegment_049_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1188 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1201 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1188 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1188 13 14, g32p_row02_traceSegment_049_1188_0013, g32p_row02_traceSegment_049_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1215 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1228 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1215 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1215 13 14, g32p_row02_traceSegment_049_1215_0013, g32p_row02_traceSegment_049_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1188 54 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1188 27 27, g32p_row02_traceSegment_049_1188_0027, g32p_row02_traceSegment_049_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1242 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1255 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1242 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1242 13 14, g32p_row02_traceSegment_049_1242_0013, g32p_row02_traceSegment_049_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1269 13 14, g32p_row02_traceSegment_049_1269_0013, g32p_row02_traceSegment_049_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1242 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1242 27 27, g32p_row02_traceSegment_049_1242_0027, g32p_row02_traceSegment_049_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1188 108 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1188 54 54, g32p_row02_traceSegment_049_1188_0054, g32p_row02_traceSegment_049_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 1080 216 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1080 108 108, g32p_row02_traceSegment_049_1080_0108, g32p_row02_traceSegment_049_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 864 432 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 864 216 216, g32p_row02_traceSegment_049_0864_0216, g32p_row02_traceSegment_049_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1296 13 14, g32p_row02_traceSegment_049_1296_0013, g32p_row02_traceSegment_049_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1323 13 14, g32p_row02_traceSegment_049_1323_0013, g32p_row02_traceSegment_049_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1296 27 27, g32p_row02_traceSegment_049_1296_0027, g32p_row02_traceSegment_049_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1350 13 14, g32p_row02_traceSegment_049_1350_0013, g32p_row02_traceSegment_049_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1377 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1390 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1377 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1377 13 14, g32p_row02_traceSegment_049_1377_0013, g32p_row02_traceSegment_049_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1350 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1350 27 27, g32p_row02_traceSegment_049_1350_0027, g32p_row02_traceSegment_049_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1296 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1296 54 54, g32p_row02_traceSegment_049_1296_0054, g32p_row02_traceSegment_049_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1417 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1404 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1404 13 14, g32p_row02_traceSegment_049_1404_0013, g32p_row02_traceSegment_049_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1431 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1444 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1431 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1431 13 14, g32p_row02_traceSegment_049_1431_0013, g32p_row02_traceSegment_049_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1404 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1404 27 27, g32p_row02_traceSegment_049_1404_0027, g32p_row02_traceSegment_049_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1458 13 14, g32p_row02_traceSegment_049_1458_0013, g32p_row02_traceSegment_049_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1485 13 14, g32p_row02_traceSegment_049_1485_0013, g32p_row02_traceSegment_049_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1458 27 27, g32p_row02_traceSegment_049_1458_0027, g32p_row02_traceSegment_049_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1404 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1404 54 54, g32p_row02_traceSegment_049_1404_0054, g32p_row02_traceSegment_049_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 1296 216 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1296 108 108, g32p_row02_traceSegment_049_1296_0108, g32p_row02_traceSegment_049_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1512 13 14, g32p_row02_traceSegment_049_1512_0013, g32p_row02_traceSegment_049_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1539 13 14, g32p_row02_traceSegment_049_1539_0013, g32p_row02_traceSegment_049_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1512 27 27, g32p_row02_traceSegment_049_1512_0027, g32p_row02_traceSegment_049_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1566 13 14, g32p_row02_traceSegment_049_1566_0013, g32p_row02_traceSegment_049_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1593 13 14, g32p_row02_traceSegment_049_1593_0013, g32p_row02_traceSegment_049_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1566 27 27, g32p_row02_traceSegment_049_1566_0027, g32p_row02_traceSegment_049_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1512 54 54, g32p_row02_traceSegment_049_1512_0054, g32p_row02_traceSegment_049_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1620 13 14, g32p_row02_traceSegment_049_1620_0013, g32p_row02_traceSegment_049_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1647 13 14, g32p_row02_traceSegment_049_1647_0013, g32p_row02_traceSegment_049_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1620 27 27, g32p_row02_traceSegment_049_1620_0027, g32p_row02_traceSegment_049_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1674 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1687 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1674 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1674 13 14, g32p_row02_traceSegment_049_1674_0013, g32p_row02_traceSegment_049_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1701 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1714 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1701 27 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1701 13 14, g32p_row02_traceSegment_049_1701_0013, g32p_row02_traceSegment_049_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1674 54 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1674 27 27, g32p_row02_traceSegment_049_1674_0027, g32p_row02_traceSegment_049_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1620 108 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1620 54 54, g32p_row02_traceSegment_049_1620_0054, g32p_row02_traceSegment_049_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 1512 216 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1512 108 108, g32p_row02_traceSegment_049_1512_0108, g32p_row02_traceSegment_049_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 1296 432 = [0, 0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1296 216 216, g32p_row02_traceSegment_049_1296_0216, g32p_row02_traceSegment_049_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_049 864 864 = [0, 0, 0, 0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 864 432 432, g32p_row02_traceSegment_049_0864_0432, g32p_row02_traceSegment_049_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_049 0 1728 = [0, 0, 0, 0, 0, 41] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 864 864, g32p_row02_traceSegment_049_0000_0864, g32p_row02_traceSegment_049_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1741 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1728 13 14, g32p_row02_traceSegment_049_1728_0013, g32p_row02_traceSegment_049_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1755 13 14, g32p_row02_traceSegment_049_1755_0013, g32p_row02_traceSegment_049_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1728 27 27, g32p_row02_traceSegment_049_1728_0027, g32p_row02_traceSegment_049_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1782 13 14, g32p_row02_traceSegment_049_1782_0013, g32p_row02_traceSegment_049_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1822 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1809 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1809 13 14, g32p_row02_traceSegment_049_1809_0013, g32p_row02_traceSegment_049_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1782 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1782 27 27, g32p_row02_traceSegment_049_1782_0027, g32p_row02_traceSegment_049_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 108 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1728 54 54, g32p_row02_traceSegment_049_1728_0054, g32p_row02_traceSegment_049_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1836 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1849 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1836 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1836 13 14, g32p_row02_traceSegment_049_1836_0013, g32p_row02_traceSegment_049_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1863 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1876 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1863 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1863 13 14, g32p_row02_traceSegment_049_1863_0013, g32p_row02_traceSegment_049_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1836 54 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1836 27 27, g32p_row02_traceSegment_049_1836_0027, g32p_row02_traceSegment_049_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1890 13 14, g32p_row02_traceSegment_049_1890_0013, g32p_row02_traceSegment_049_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1917 13 14, g32p_row02_traceSegment_049_1917_0013, g32p_row02_traceSegment_049_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1890 27 27, g32p_row02_traceSegment_049_1890_0027, g32p_row02_traceSegment_049_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1836 108 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1836 54 54, g32p_row02_traceSegment_049_1836_0054, g32p_row02_traceSegment_049_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 216 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1728 108 108, g32p_row02_traceSegment_049_1728_0108, g32p_row02_traceSegment_049_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1944 13 14, g32p_row02_traceSegment_049_1944_0013, g32p_row02_traceSegment_049_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1971 13 14, g32p_row02_traceSegment_049_1971_0013, g32p_row02_traceSegment_049_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1944 27 27, g32p_row02_traceSegment_049_1944_0027, g32p_row02_traceSegment_049_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 1998 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2011 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 1998 27 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1998 13 14, g32p_row02_traceSegment_049_1998_0013, g32p_row02_traceSegment_049_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2025 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2038 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2025 27 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2025 13 14, g32p_row02_traceSegment_049_2025_0013, g32p_row02_traceSegment_049_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 1998 54 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1998 27 27, g32p_row02_traceSegment_049_1998_0027, g32p_row02_traceSegment_049_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 1944 108 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1944 54 54, g32p_row02_traceSegment_049_1944_0054, g32p_row02_traceSegment_049_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2052 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2065 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2052 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2052 13 14, g32p_row02_traceSegment_049_2052_0013, g32p_row02_traceSegment_049_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2079 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2092 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2079 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2079 13 14, g32p_row02_traceSegment_049_2079_0013, g32p_row02_traceSegment_049_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2052 54 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2052 27 27, g32p_row02_traceSegment_049_2052_0027, g32p_row02_traceSegment_049_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2106 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2106 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2106 13 14, g32p_row02_traceSegment_049_2106_0013, g32p_row02_traceSegment_049_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2133 13 14, g32p_row02_traceSegment_049_2133_0013, g32p_row02_traceSegment_049_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2106 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2106 27 27, g32p_row02_traceSegment_049_2106_0027, g32p_row02_traceSegment_049_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2052 108 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2052 54 54, g32p_row02_traceSegment_049_2052_0054, g32p_row02_traceSegment_049_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 1944 216 = [0, 0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1944 108 108, g32p_row02_traceSegment_049_1944_0108, g32p_row02_traceSegment_049_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 432 = [0, 0, 0, 0, 0, 39] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1728 216 216, g32p_row02_traceSegment_049_1728_0216, g32p_row02_traceSegment_049_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2160 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2160 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2160 13 14, g32p_row02_traceSegment_049_2160_0013, g32p_row02_traceSegment_049_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2187 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2200 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2187 27 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2187 13 14, g32p_row02_traceSegment_049_2187_0013, g32p_row02_traceSegment_049_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2160 54 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2160 27 27, g32p_row02_traceSegment_049_2160_0027, g32p_row02_traceSegment_049_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2214 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2227 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2214 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2214 13 14, g32p_row02_traceSegment_049_2214_0013, g32p_row02_traceSegment_049_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2241 13 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2254 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2241 27 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2241 13 14, g32p_row02_traceSegment_049_2241_0013, g32p_row02_traceSegment_049_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2214 54 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2214 27 27, g32p_row02_traceSegment_049_2214_0027, g32p_row02_traceSegment_049_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2160 108 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2160 54 54, g32p_row02_traceSegment_049_2160_0054, g32p_row02_traceSegment_049_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2268 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2281 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2268 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2268 13 14, g32p_row02_traceSegment_049_2268_0013, g32p_row02_traceSegment_049_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2295 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2308 14 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2295 27 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2295 13 14, g32p_row02_traceSegment_049_2295_0013, g32p_row02_traceSegment_049_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2268 54 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2268 27 27, g32p_row02_traceSegment_049_2268_0027, g32p_row02_traceSegment_049_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2322 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2335 14 = [0, 0, 0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2322 27 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2322 13 14, g32p_row02_traceSegment_049_2322_0013, g32p_row02_traceSegment_049_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2349 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2349 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2349 13 14, g32p_row02_traceSegment_049_2349_0013, g32p_row02_traceSegment_049_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2322 54 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2322 27 27, g32p_row02_traceSegment_049_2322_0027, g32p_row02_traceSegment_049_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2268 108 = [0, 0, 0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2268 54 54, g32p_row02_traceSegment_049_2268_0054, g32p_row02_traceSegment_049_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 2160 216 = [0, 0, 0, 0, 0, 40] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2160 108 108, g32p_row02_traceSegment_049_2160_0108, g32p_row02_traceSegment_049_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2376 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2389 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2376 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2376 13 14, g32p_row02_traceSegment_049_2376_0013, g32p_row02_traceSegment_049_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2416 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2403 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2403 13 14, g32p_row02_traceSegment_049_2403_0013, g32p_row02_traceSegment_049_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2376 54 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2376 27 27, g32p_row02_traceSegment_049_2376_0027, g32p_row02_traceSegment_049_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2430 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2430 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2430 13 14, g32p_row02_traceSegment_049_2430_0013, g32p_row02_traceSegment_049_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2457 13 14, g32p_row02_traceSegment_049_2457_0013, g32p_row02_traceSegment_049_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2430 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2430 27 27, g32p_row02_traceSegment_049_2430_0027, g32p_row02_traceSegment_049_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2376 108 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2376 54 54, g32p_row02_traceSegment_049_2376_0054, g32p_row02_traceSegment_049_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2484 13 14, g32p_row02_traceSegment_049_2484_0013, g32p_row02_traceSegment_049_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2511 13 14, g32p_row02_traceSegment_049_2511_0013, g32p_row02_traceSegment_049_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2484 27 27, g32p_row02_traceSegment_049_2484_0027, g32p_row02_traceSegment_049_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2538 13 14, g32p_row02_traceSegment_049_2538_0013, g32p_row02_traceSegment_049_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2578 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2565 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2565 13 14, g32p_row02_traceSegment_049_2565_0013, g32p_row02_traceSegment_049_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2538 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2538 27 27, g32p_row02_traceSegment_049_2538_0027, g32p_row02_traceSegment_049_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2484 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2484 54 54, g32p_row02_traceSegment_049_2484_0054, g32p_row02_traceSegment_049_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 2376 216 = [0, 0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2376 108 108, g32p_row02_traceSegment_049_2376_0108, g32p_row02_traceSegment_049_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 2160 432 = [0, 0, 0, 0, 0, 49] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2160 216 216, g32p_row02_traceSegment_049_2160_0216, g32p_row02_traceSegment_049_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 864 = [0, 0, 0, 0, 0, 88] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1728 432 432, g32p_row02_traceSegment_049_1728_0432, g32p_row02_traceSegment_049_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2592 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2592 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2592 13 14, g32p_row02_traceSegment_049_2592_0013, g32p_row02_traceSegment_049_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2619 13 14, g32p_row02_traceSegment_049_2619_0013, g32p_row02_traceSegment_049_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2592 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2592 27 27, g32p_row02_traceSegment_049_2592_0027, g32p_row02_traceSegment_049_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2659 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2646 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2646 13 14, g32p_row02_traceSegment_049_2646_0013, g32p_row02_traceSegment_049_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2686 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2673 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2673 13 14, g32p_row02_traceSegment_049_2673_0013, g32p_row02_traceSegment_049_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2646 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2646 27 27, g32p_row02_traceSegment_049_2646_0027, g32p_row02_traceSegment_049_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2592 108 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2592 54 54, g32p_row02_traceSegment_049_2592_0054, g32p_row02_traceSegment_049_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2700 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2713 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2700 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2700 13 14, g32p_row02_traceSegment_049_2700_0013, g32p_row02_traceSegment_049_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2727 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2727 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2727 13 14, g32p_row02_traceSegment_049_2727_0013, g32p_row02_traceSegment_049_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2700 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2700 27 27, g32p_row02_traceSegment_049_2700_0027, g32p_row02_traceSegment_049_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2754 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2767 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2754 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2754 13 14, g32p_row02_traceSegment_049_2754_0013, g32p_row02_traceSegment_049_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2781 13 14, g32p_row02_traceSegment_049_2781_0013, g32p_row02_traceSegment_049_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2754 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2754 27 27, g32p_row02_traceSegment_049_2754_0027, g32p_row02_traceSegment_049_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2700 108 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2700 54 54, g32p_row02_traceSegment_049_2700_0054, g32p_row02_traceSegment_049_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 2592 216 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2592 108 108, g32p_row02_traceSegment_049_2592_0108, g32p_row02_traceSegment_049_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2808 13 14, g32p_row02_traceSegment_049_2808_0013, g32p_row02_traceSegment_049_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2835 13 14, g32p_row02_traceSegment_049_2835_0013, g32p_row02_traceSegment_049_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2808 27 27, g32p_row02_traceSegment_049_2808_0027, g32p_row02_traceSegment_049_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2862 13 14, g32p_row02_traceSegment_049_2862_0013, g32p_row02_traceSegment_049_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2889 13 14, g32p_row02_traceSegment_049_2889_0013, g32p_row02_traceSegment_049_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2862 27 27, g32p_row02_traceSegment_049_2862_0027, g32p_row02_traceSegment_049_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2808 54 54, g32p_row02_traceSegment_049_2808_0054, g32p_row02_traceSegment_049_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2916 13 14, g32p_row02_traceSegment_049_2916_0013, g32p_row02_traceSegment_049_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2943 13 14, g32p_row02_traceSegment_049_2943_0013, g32p_row02_traceSegment_049_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2916 27 27, g32p_row02_traceSegment_049_2916_0027, g32p_row02_traceSegment_049_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2970 13 14, g32p_row02_traceSegment_049_2970_0013, g32p_row02_traceSegment_049_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2997 13 14, g32p_row02_traceSegment_049_2997_0013, g32p_row02_traceSegment_049_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2970 27 27, g32p_row02_traceSegment_049_2970_0027, g32p_row02_traceSegment_049_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2916 54 54, g32p_row02_traceSegment_049_2916_0054, g32p_row02_traceSegment_049_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2808 108 108, g32p_row02_traceSegment_049_2808_0108, g32p_row02_traceSegment_049_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 2592 432 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2592 216 216, g32p_row02_traceSegment_049_2592_0216, g32p_row02_traceSegment_049_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3024 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3024 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3024 13 14, g32p_row02_traceSegment_049_3024_0013, g32p_row02_traceSegment_049_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3051 13 14, g32p_row02_traceSegment_049_3051_0013, g32p_row02_traceSegment_049_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3024 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3024 27 27, g32p_row02_traceSegment_049_3024_0027, g32p_row02_traceSegment_049_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3078 13 14, g32p_row02_traceSegment_049_3078_0013, g32p_row02_traceSegment_049_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3105 13 14, g32p_row02_traceSegment_049_3105_0013, g32p_row02_traceSegment_049_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3078 27 27, g32p_row02_traceSegment_049_3078_0027, g32p_row02_traceSegment_049_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 3024 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3024 54 54, g32p_row02_traceSegment_049_3024_0054, g32p_row02_traceSegment_049_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3132 13 14, g32p_row02_traceSegment_049_3132_0013, g32p_row02_traceSegment_049_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3159 13 14, g32p_row02_traceSegment_049_3159_0013, g32p_row02_traceSegment_049_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3132 27 27, g32p_row02_traceSegment_049_3132_0027, g32p_row02_traceSegment_049_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3186 13 14, g32p_row02_traceSegment_049_3186_0013, g32p_row02_traceSegment_049_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3213 13 14, g32p_row02_traceSegment_049_3213_0013, g32p_row02_traceSegment_049_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3186 27 27, g32p_row02_traceSegment_049_3186_0027, g32p_row02_traceSegment_049_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3132 54 54, g32p_row02_traceSegment_049_3132_0054, g32p_row02_traceSegment_049_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 3024 216 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3024 108 108, g32p_row02_traceSegment_049_3024_0108, g32p_row02_traceSegment_049_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3240 13 14, g32p_row02_traceSegment_049_3240_0013, g32p_row02_traceSegment_049_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3267 13 14, g32p_row02_traceSegment_049_3267_0013, g32p_row02_traceSegment_049_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3240 27 27, g32p_row02_traceSegment_049_3240_0027, g32p_row02_traceSegment_049_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3294 13 14, g32p_row02_traceSegment_049_3294_0013, g32p_row02_traceSegment_049_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3321 13 14, g32p_row02_traceSegment_049_3321_0013, g32p_row02_traceSegment_049_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3294 27 27, g32p_row02_traceSegment_049_3294_0027, g32p_row02_traceSegment_049_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3240 54 54, g32p_row02_traceSegment_049_3240_0054, g32p_row02_traceSegment_049_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3348 13 14, g32p_row02_traceSegment_049_3348_0013, g32p_row02_traceSegment_049_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3375 13 14, g32p_row02_traceSegment_049_3375_0013, g32p_row02_traceSegment_049_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3348 27 27, g32p_row02_traceSegment_049_3348_0027, g32p_row02_traceSegment_049_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3402 13 14, g32p_row02_traceSegment_049_3402_0013, g32p_row02_traceSegment_049_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_049 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_049 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_049_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_049 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3429 13 14, g32p_row02_traceSegment_049_3429_0013, g32p_row02_traceSegment_049_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_049 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3402 27 27, g32p_row02_traceSegment_049_3402_0027, g32p_row02_traceSegment_049_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_049 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3348 54 54, g32p_row02_traceSegment_049_3348_0054, g32p_row02_traceSegment_049_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_049 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3240 108 108, g32p_row02_traceSegment_049_3240_0108, g32p_row02_traceSegment_049_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_049_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_049 3024 432 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 3024 216 216, g32p_row02_traceSegment_049_3024_0216, g32p_row02_traceSegment_049_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_049_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_049 2592 864 = [0, 0, 0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 2592 432 432, g32p_row02_traceSegment_049_2592_0432, g32p_row02_traceSegment_049_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_049_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_049 1728 1728 = [0, 0, 0, 0, 0, 103] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 1728 864 864, g32p_row02_traceSegment_049_1728_0864, g32p_row02_traceSegment_049_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_049_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_049 0 3456 = [0, 0, 0, 0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_049 0 1728 1728, g32p_row02_traceSegment_049_0000_1728, g32p_row02_traceSegment_049_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_049 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 49 = [0, 0, 0, 0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_049_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_050 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 50 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_050_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 13 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 0 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 13 14, g32p_row02_traceSegment_050_0000_0013, g32p_row02_traceSegment_050_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 27 13 14, g32p_row02_traceSegment_050_0027_0013, g32p_row02_traceSegment_050_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 0 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 27 27, g32p_row02_traceSegment_050_0000_0027, g32p_row02_traceSegment_050_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 54 13 14, g32p_row02_traceSegment_050_0054_0013, g32p_row02_traceSegment_050_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 81 13 = [1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 94 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 81 27 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 81 13 14, g32p_row02_traceSegment_050_0081_0013, g32p_row02_traceSegment_050_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 54 54 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 54 27 27, g32p_row02_traceSegment_050_0054_0027, g32p_row02_traceSegment_050_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 0 108 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 54 54, g32p_row02_traceSegment_050_0000_0054, g32p_row02_traceSegment_050_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 108 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 121 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 108 27 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 108 13 14, g32p_row02_traceSegment_050_0108_0013, g32p_row02_traceSegment_050_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 135 13 14, g32p_row02_traceSegment_050_0135_0013, g32p_row02_traceSegment_050_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 108 54 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 108 27 27, g32p_row02_traceSegment_050_0108_0027, g32p_row02_traceSegment_050_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 162 13 14, g32p_row02_traceSegment_050_0162_0013, g32p_row02_traceSegment_050_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 189 13 14, g32p_row02_traceSegment_050_0189_0013, g32p_row02_traceSegment_050_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 162 27 27, g32p_row02_traceSegment_050_0162_0027, g32p_row02_traceSegment_050_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 108 108 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 108 54 54, g32p_row02_traceSegment_050_0108_0054, g32p_row02_traceSegment_050_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 0 216 = [3, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 108 108, g32p_row02_traceSegment_050_0000_0108, g32p_row02_traceSegment_050_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 216 13 14, g32p_row02_traceSegment_050_0216_0013, g32p_row02_traceSegment_050_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 243 13 14, g32p_row02_traceSegment_050_0243_0013, g32p_row02_traceSegment_050_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 216 27 27, g32p_row02_traceSegment_050_0216_0027, g32p_row02_traceSegment_050_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 283 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 270 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 270 13 14, g32p_row02_traceSegment_050_0270_0013, g32p_row02_traceSegment_050_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 297 13 14, g32p_row02_traceSegment_050_0297_0013, g32p_row02_traceSegment_050_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 270 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 270 27 27, g32p_row02_traceSegment_050_0270_0027, g32p_row02_traceSegment_050_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 216 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 216 54 54, g32p_row02_traceSegment_050_0216_0054, g32p_row02_traceSegment_050_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 324 13 14, g32p_row02_traceSegment_050_0324_0013, g32p_row02_traceSegment_050_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 351 13 14, g32p_row02_traceSegment_050_0351_0013, g32p_row02_traceSegment_050_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 324 27 27, g32p_row02_traceSegment_050_0324_0027, g32p_row02_traceSegment_050_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 378 13 14, g32p_row02_traceSegment_050_0378_0013, g32p_row02_traceSegment_050_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 405 13 14, g32p_row02_traceSegment_050_0405_0013, g32p_row02_traceSegment_050_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 378 27 27, g32p_row02_traceSegment_050_0378_0027, g32p_row02_traceSegment_050_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 324 54 54, g32p_row02_traceSegment_050_0324_0054, g32p_row02_traceSegment_050_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 216 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 216 108 108, g32p_row02_traceSegment_050_0216_0108, g32p_row02_traceSegment_050_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 0 432 = [3, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 216 216, g32p_row02_traceSegment_050_0000_0216, g32p_row02_traceSegment_050_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 432 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 445 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 432 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 432 13 14, g32p_row02_traceSegment_050_0432_0013, g32p_row02_traceSegment_050_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 459 13 14, g32p_row02_traceSegment_050_0459_0013, g32p_row02_traceSegment_050_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 432 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 432 27 27, g32p_row02_traceSegment_050_0432_0027, g32p_row02_traceSegment_050_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 486 13 = [1, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 486 27 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 486 13 14, g32p_row02_traceSegment_050_0486_0013, g32p_row02_traceSegment_050_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 513 13 14, g32p_row02_traceSegment_050_0513_0013, g32p_row02_traceSegment_050_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 486 54 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 486 27 27, g32p_row02_traceSegment_050_0486_0027, g32p_row02_traceSegment_050_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 432 108 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 432 54 54, g32p_row02_traceSegment_050_0432_0054, g32p_row02_traceSegment_050_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 540 13 14, g32p_row02_traceSegment_050_0540_0013, g32p_row02_traceSegment_050_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 567 13 14, g32p_row02_traceSegment_050_0567_0013, g32p_row02_traceSegment_050_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 540 27 27, g32p_row02_traceSegment_050_0540_0027, g32p_row02_traceSegment_050_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 594 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 607 14 = [0, 8] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 594 27 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 594 13 14, g32p_row02_traceSegment_050_0594_0013, g32p_row02_traceSegment_050_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 621 13 14, g32p_row02_traceSegment_050_0621_0013, g32p_row02_traceSegment_050_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 594 54 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 594 27 27, g32p_row02_traceSegment_050_0594_0027, g32p_row02_traceSegment_050_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 540 108 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 540 54 54, g32p_row02_traceSegment_050_0540_0054, g32p_row02_traceSegment_050_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 432 216 = [4, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 432 108 108, g32p_row02_traceSegment_050_0432_0108, g32p_row02_traceSegment_050_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 648 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 661 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 648 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 648 13 14, g32p_row02_traceSegment_050_0648_0013, g32p_row02_traceSegment_050_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 675 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 688 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 675 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 675 13 14, g32p_row02_traceSegment_050_0675_0013, g32p_row02_traceSegment_050_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 648 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 648 27 27, g32p_row02_traceSegment_050_0648_0027, g32p_row02_traceSegment_050_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 702 13 14, g32p_row02_traceSegment_050_0702_0013, g32p_row02_traceSegment_050_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 729 13 14, g32p_row02_traceSegment_050_0729_0013, g32p_row02_traceSegment_050_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 702 27 27, g32p_row02_traceSegment_050_0702_0027, g32p_row02_traceSegment_050_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 648 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 648 54 54, g32p_row02_traceSegment_050_0648_0054, g32p_row02_traceSegment_050_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 769 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 756 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 756 13 14, g32p_row02_traceSegment_050_0756_0013, g32p_row02_traceSegment_050_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 783 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 783 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 783 13 14, g32p_row02_traceSegment_050_0783_0013, g32p_row02_traceSegment_050_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 756 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 756 27 27, g32p_row02_traceSegment_050_0756_0027, g32p_row02_traceSegment_050_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 823 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 810 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 810 13 14, g32p_row02_traceSegment_050_0810_0013, g32p_row02_traceSegment_050_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 837 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 837 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 837 13 14, g32p_row02_traceSegment_050_0837_0013, g32p_row02_traceSegment_050_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 810 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 810 27 27, g32p_row02_traceSegment_050_0810_0027, g32p_row02_traceSegment_050_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 756 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 756 54 54, g32p_row02_traceSegment_050_0756_0054, g32p_row02_traceSegment_050_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 648 216 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 648 108 108, g32p_row02_traceSegment_050_0648_0108, g32p_row02_traceSegment_050_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 432 432 = [4, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 432 216 216, g32p_row02_traceSegment_050_0432_0216, g32p_row02_traceSegment_050_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_050 0 864 = [7, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 432 432, g32p_row02_traceSegment_050_0000_0432, g32p_row02_traceSegment_050_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 877 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 864 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 864 13 14, g32p_row02_traceSegment_050_0864_0013, g32p_row02_traceSegment_050_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 891 13 14, g32p_row02_traceSegment_050_0891_0013, g32p_row02_traceSegment_050_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 864 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 864 27 27, g32p_row02_traceSegment_050_0864_0027, g32p_row02_traceSegment_050_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 931 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 918 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 918 13 14, g32p_row02_traceSegment_050_0918_0013, g32p_row02_traceSegment_050_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 945 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 945 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 945 13 14, g32p_row02_traceSegment_050_0945_0013, g32p_row02_traceSegment_050_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 918 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 918 27 27, g32p_row02_traceSegment_050_0918_0027, g32p_row02_traceSegment_050_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 864 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 864 54 54, g32p_row02_traceSegment_050_0864_0054, g32p_row02_traceSegment_050_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 972 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 985 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 972 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 972 13 14, g32p_row02_traceSegment_050_0972_0013, g32p_row02_traceSegment_050_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 999 13 14, g32p_row02_traceSegment_050_0999_0013, g32p_row02_traceSegment_050_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 972 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 972 27 27, g32p_row02_traceSegment_050_0972_0027, g32p_row02_traceSegment_050_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1026 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1026 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1026 13 14, g32p_row02_traceSegment_050_1026_0013, g32p_row02_traceSegment_050_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1053 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1053 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1053 13 14, g32p_row02_traceSegment_050_1053_0013, g32p_row02_traceSegment_050_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1026 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1026 27 27, g32p_row02_traceSegment_050_1026_0027, g32p_row02_traceSegment_050_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 972 108 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 972 54 54, g32p_row02_traceSegment_050_0972_0054, g32p_row02_traceSegment_050_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 864 216 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 864 108 108, g32p_row02_traceSegment_050_0864_0108, g32p_row02_traceSegment_050_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1080 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1093 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1080 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1080 13 14, g32p_row02_traceSegment_050_1080_0013, g32p_row02_traceSegment_050_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1107 13 14, g32p_row02_traceSegment_050_1107_0013, g32p_row02_traceSegment_050_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1080 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1080 27 27, g32p_row02_traceSegment_050_1080_0027, g32p_row02_traceSegment_050_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1134 13 14, g32p_row02_traceSegment_050_1134_0013, g32p_row02_traceSegment_050_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1161 13 14, g32p_row02_traceSegment_050_1161_0013, g32p_row02_traceSegment_050_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1134 27 27, g32p_row02_traceSegment_050_1134_0027, g32p_row02_traceSegment_050_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1080 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1080 54 54, g32p_row02_traceSegment_050_1080_0054, g32p_row02_traceSegment_050_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1188 13 14, g32p_row02_traceSegment_050_1188_0013, g32p_row02_traceSegment_050_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1215 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1228 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1215 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1215 13 14, g32p_row02_traceSegment_050_1215_0013, g32p_row02_traceSegment_050_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1188 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1188 27 27, g32p_row02_traceSegment_050_1188_0027, g32p_row02_traceSegment_050_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1242 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1255 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1242 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1242 13 14, g32p_row02_traceSegment_050_1242_0013, g32p_row02_traceSegment_050_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1269 13 = [1, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1282 14 = [1, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1269 27 = [2, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1269 13 14, g32p_row02_traceSegment_050_1269_0013, g32p_row02_traceSegment_050_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1242 54 = [3, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1242 27 27, g32p_row02_traceSegment_050_1242_0027, g32p_row02_traceSegment_050_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1188 108 = [6, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1188 54 54, g32p_row02_traceSegment_050_1188_0054, g32p_row02_traceSegment_050_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 1080 216 = [6, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1080 108 108, g32p_row02_traceSegment_050_1080_0108, g32p_row02_traceSegment_050_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 864 432 = [6, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 864 216 216, g32p_row02_traceSegment_050_0864_0216, g32p_row02_traceSegment_050_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1296 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1296 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1296 13 14, g32p_row02_traceSegment_050_1296_0013, g32p_row02_traceSegment_050_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1323 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1323 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1323 13 14, g32p_row02_traceSegment_050_1323_0013, g32p_row02_traceSegment_050_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1296 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1296 27 27, g32p_row02_traceSegment_050_1296_0027, g32p_row02_traceSegment_050_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1350 13 14, g32p_row02_traceSegment_050_1350_0013, g32p_row02_traceSegment_050_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1377 13 14, g32p_row02_traceSegment_050_1377_0013, g32p_row02_traceSegment_050_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1350 27 27, g32p_row02_traceSegment_050_1350_0027, g32p_row02_traceSegment_050_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1296 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1296 54 54, g32p_row02_traceSegment_050_1296_0054, g32p_row02_traceSegment_050_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1404 13 14, g32p_row02_traceSegment_050_1404_0013, g32p_row02_traceSegment_050_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1431 13 14, g32p_row02_traceSegment_050_1431_0013, g32p_row02_traceSegment_050_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1404 27 27, g32p_row02_traceSegment_050_1404_0027, g32p_row02_traceSegment_050_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1458 13 14, g32p_row02_traceSegment_050_1458_0013, g32p_row02_traceSegment_050_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1485 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1485 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1485 13 14, g32p_row02_traceSegment_050_1485_0013, g32p_row02_traceSegment_050_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1458 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1458 27 27, g32p_row02_traceSegment_050_1458_0027, g32p_row02_traceSegment_050_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1404 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1404 54 54, g32p_row02_traceSegment_050_1404_0054, g32p_row02_traceSegment_050_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 1296 216 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1296 108 108, g32p_row02_traceSegment_050_1296_0108, g32p_row02_traceSegment_050_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1512 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1512 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1512 13 14, g32p_row02_traceSegment_050_1512_0013, g32p_row02_traceSegment_050_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1539 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1552 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1539 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1539 13 14, g32p_row02_traceSegment_050_1539_0013, g32p_row02_traceSegment_050_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1512 54 = [1, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1512 27 27, g32p_row02_traceSegment_050_1512_0027, g32p_row02_traceSegment_050_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1566 13 14, g32p_row02_traceSegment_050_1566_0013, g32p_row02_traceSegment_050_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1593 13 14, g32p_row02_traceSegment_050_1593_0013, g32p_row02_traceSegment_050_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1566 27 27, g32p_row02_traceSegment_050_1566_0027, g32p_row02_traceSegment_050_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1512 108 = [1, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1512 54 54, g32p_row02_traceSegment_050_1512_0054, g32p_row02_traceSegment_050_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1620 13 14, g32p_row02_traceSegment_050_1620_0013, g32p_row02_traceSegment_050_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1647 13 14, g32p_row02_traceSegment_050_1647_0013, g32p_row02_traceSegment_050_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1620 27 27, g32p_row02_traceSegment_050_1620_0027, g32p_row02_traceSegment_050_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1674 13 14, g32p_row02_traceSegment_050_1674_0013, g32p_row02_traceSegment_050_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1701 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1714 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1701 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1701 13 14, g32p_row02_traceSegment_050_1701_0013, g32p_row02_traceSegment_050_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1674 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1674 27 27, g32p_row02_traceSegment_050_1674_0027, g32p_row02_traceSegment_050_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1620 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1620 54 54, g32p_row02_traceSegment_050_1620_0054, g32p_row02_traceSegment_050_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 1512 216 = [3, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1512 108 108, g32p_row02_traceSegment_050_1512_0108, g32p_row02_traceSegment_050_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 1296 432 = [3, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1296 216 216, g32p_row02_traceSegment_050_1296_0216, g32p_row02_traceSegment_050_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_050 864 864 = [9, 36] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 864 432 432, g32p_row02_traceSegment_050_0864_0432, g32p_row02_traceSegment_050_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_050 0 1728 = [16, 66] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 864 864, g32p_row02_traceSegment_050_0000_0864, g32p_row02_traceSegment_050_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1741 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1728 13 14, g32p_row02_traceSegment_050_1728_0013, g32p_row02_traceSegment_050_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1755 13 = [1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1755 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1755 13 14, g32p_row02_traceSegment_050_1755_0013, g32p_row02_traceSegment_050_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 54 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1728 27 27, g32p_row02_traceSegment_050_1728_0027, g32p_row02_traceSegment_050_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1782 13 14, g32p_row02_traceSegment_050_1782_0013, g32p_row02_traceSegment_050_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1809 13 14, g32p_row02_traceSegment_050_1809_0013, g32p_row02_traceSegment_050_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1782 27 27, g32p_row02_traceSegment_050_1782_0027, g32p_row02_traceSegment_050_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 108 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1728 54 54, g32p_row02_traceSegment_050_1728_0054, g32p_row02_traceSegment_050_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1836 13 14, g32p_row02_traceSegment_050_1836_0013, g32p_row02_traceSegment_050_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1863 13 14, g32p_row02_traceSegment_050_1863_0013, g32p_row02_traceSegment_050_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1836 27 27, g32p_row02_traceSegment_050_1836_0027, g32p_row02_traceSegment_050_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1903 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1890 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1890 13 14, g32p_row02_traceSegment_050_1890_0013, g32p_row02_traceSegment_050_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1917 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1917 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1917 13 14, g32p_row02_traceSegment_050_1917_0013, g32p_row02_traceSegment_050_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1890 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1890 27 27, g32p_row02_traceSegment_050_1890_0027, g32p_row02_traceSegment_050_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1836 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1836 54 54, g32p_row02_traceSegment_050_1836_0054, g32p_row02_traceSegment_050_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 216 = [1, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1728 108 108, g32p_row02_traceSegment_050_1728_0108, g32p_row02_traceSegment_050_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1944 13 14, g32p_row02_traceSegment_050_1944_0013, g32p_row02_traceSegment_050_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1971 13 14, g32p_row02_traceSegment_050_1971_0013, g32p_row02_traceSegment_050_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1944 27 27, g32p_row02_traceSegment_050_1944_0027, g32p_row02_traceSegment_050_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1998 13 14, g32p_row02_traceSegment_050_1998_0013, g32p_row02_traceSegment_050_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2038 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2025 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2025 13 14, g32p_row02_traceSegment_050_2025_0013, g32p_row02_traceSegment_050_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 1998 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1998 27 27, g32p_row02_traceSegment_050_1998_0027, g32p_row02_traceSegment_050_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 1944 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1944 54 54, g32p_row02_traceSegment_050_1944_0054, g32p_row02_traceSegment_050_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2052 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2065 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2052 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2052 13 14, g32p_row02_traceSegment_050_2052_0013, g32p_row02_traceSegment_050_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2092 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2079 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2079 13 14, g32p_row02_traceSegment_050_2079_0013, g32p_row02_traceSegment_050_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2052 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2052 27 27, g32p_row02_traceSegment_050_2052_0027, g32p_row02_traceSegment_050_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2119 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2106 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2106 13 14, g32p_row02_traceSegment_050_2106_0013, g32p_row02_traceSegment_050_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2133 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2146 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2133 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2133 13 14, g32p_row02_traceSegment_050_2133_0013, g32p_row02_traceSegment_050_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2106 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2106 27 27, g32p_row02_traceSegment_050_2106_0027, g32p_row02_traceSegment_050_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2052 108 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2052 54 54, g32p_row02_traceSegment_050_2052_0054, g32p_row02_traceSegment_050_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 1944 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1944 108 108, g32p_row02_traceSegment_050_1944_0108, g32p_row02_traceSegment_050_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 432 = [9, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1728 216 216, g32p_row02_traceSegment_050_1728_0216, g32p_row02_traceSegment_050_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2160 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2160 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2160 13 14, g32p_row02_traceSegment_050_2160_0013, g32p_row02_traceSegment_050_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2187 13 14, g32p_row02_traceSegment_050_2187_0013, g32p_row02_traceSegment_050_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2160 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2160 27 27, g32p_row02_traceSegment_050_2160_0027, g32p_row02_traceSegment_050_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2214 13 14, g32p_row02_traceSegment_050_2214_0013, g32p_row02_traceSegment_050_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2241 13 14, g32p_row02_traceSegment_050_2241_0013, g32p_row02_traceSegment_050_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2214 27 27, g32p_row02_traceSegment_050_2214_0027, g32p_row02_traceSegment_050_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2160 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2160 54 54, g32p_row02_traceSegment_050_2160_0054, g32p_row02_traceSegment_050_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2268 13 14, g32p_row02_traceSegment_050_2268_0013, g32p_row02_traceSegment_050_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2295 13 14, g32p_row02_traceSegment_050_2295_0013, g32p_row02_traceSegment_050_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2268 27 27, g32p_row02_traceSegment_050_2268_0027, g32p_row02_traceSegment_050_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2322 13 14, g32p_row02_traceSegment_050_2322_0013, g32p_row02_traceSegment_050_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2362 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2349 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2349 13 14, g32p_row02_traceSegment_050_2349_0013, g32p_row02_traceSegment_050_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2322 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2322 27 27, g32p_row02_traceSegment_050_2322_0027, g32p_row02_traceSegment_050_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2268 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2268 54 54, g32p_row02_traceSegment_050_2268_0054, g32p_row02_traceSegment_050_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 2160 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2160 108 108, g32p_row02_traceSegment_050_2160_0108, g32p_row02_traceSegment_050_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2376 13 14, g32p_row02_traceSegment_050_2376_0013, g32p_row02_traceSegment_050_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2416 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2403 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2403 13 14, g32p_row02_traceSegment_050_2403_0013, g32p_row02_traceSegment_050_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2376 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2376 27 27, g32p_row02_traceSegment_050_2376_0027, g32p_row02_traceSegment_050_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2430 13 14, g32p_row02_traceSegment_050_2430_0013, g32p_row02_traceSegment_050_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2457 13 14, g32p_row02_traceSegment_050_2457_0013, g32p_row02_traceSegment_050_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2430 27 27, g32p_row02_traceSegment_050_2430_0027, g32p_row02_traceSegment_050_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2376 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2376 54 54, g32p_row02_traceSegment_050_2376_0054, g32p_row02_traceSegment_050_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2484 13 14, g32p_row02_traceSegment_050_2484_0013, g32p_row02_traceSegment_050_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2511 13 14, g32p_row02_traceSegment_050_2511_0013, g32p_row02_traceSegment_050_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2484 27 27, g32p_row02_traceSegment_050_2484_0027, g32p_row02_traceSegment_050_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2538 13 14, g32p_row02_traceSegment_050_2538_0013, g32p_row02_traceSegment_050_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2565 13 14, g32p_row02_traceSegment_050_2565_0013, g32p_row02_traceSegment_050_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2538 27 27, g32p_row02_traceSegment_050_2538_0027, g32p_row02_traceSegment_050_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2484 54 54, g32p_row02_traceSegment_050_2484_0054, g32p_row02_traceSegment_050_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 2376 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2376 108 108, g32p_row02_traceSegment_050_2376_0108, g32p_row02_traceSegment_050_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 2160 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2160 216 216, g32p_row02_traceSegment_050_2160_0216, g32p_row02_traceSegment_050_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 864 = [9, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1728 432 432, g32p_row02_traceSegment_050_1728_0432, g32p_row02_traceSegment_050_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2592 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2605 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2592 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2592 13 14, g32p_row02_traceSegment_050_2592_0013, g32p_row02_traceSegment_050_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2619 13 14, g32p_row02_traceSegment_050_2619_0013, g32p_row02_traceSegment_050_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2592 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2592 27 27, g32p_row02_traceSegment_050_2592_0027, g32p_row02_traceSegment_050_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2646 13 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2646 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2646 13 14, g32p_row02_traceSegment_050_2646_0013, g32p_row02_traceSegment_050_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2673 13 14, g32p_row02_traceSegment_050_2673_0013, g32p_row02_traceSegment_050_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2646 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2646 27 27, g32p_row02_traceSegment_050_2646_0027, g32p_row02_traceSegment_050_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2592 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2592 54 54, g32p_row02_traceSegment_050_2592_0054, g32p_row02_traceSegment_050_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2700 13 14, g32p_row02_traceSegment_050_2700_0013, g32p_row02_traceSegment_050_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2727 13 14, g32p_row02_traceSegment_050_2727_0013, g32p_row02_traceSegment_050_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2700 27 27, g32p_row02_traceSegment_050_2700_0027, g32p_row02_traceSegment_050_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2754 13 14, g32p_row02_traceSegment_050_2754_0013, g32p_row02_traceSegment_050_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2794 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2781 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2781 13 14, g32p_row02_traceSegment_050_2781_0013, g32p_row02_traceSegment_050_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2754 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2754 27 27, g32p_row02_traceSegment_050_2754_0027, g32p_row02_traceSegment_050_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2700 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2700 54 54, g32p_row02_traceSegment_050_2700_0054, g32p_row02_traceSegment_050_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 2592 216 = [5, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2592 108 108, g32p_row02_traceSegment_050_2592_0108, g32p_row02_traceSegment_050_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2808 13 = [0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2808 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2808 13 14, g32p_row02_traceSegment_050_2808_0013, g32p_row02_traceSegment_050_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2835 13 14, g32p_row02_traceSegment_050_2835_0013, g32p_row02_traceSegment_050_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2808 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2808 27 27, g32p_row02_traceSegment_050_2808_0027, g32p_row02_traceSegment_050_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2862 13 14, g32p_row02_traceSegment_050_2862_0013, g32p_row02_traceSegment_050_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2902 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2889 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2889 13 14, g32p_row02_traceSegment_050_2889_0013, g32p_row02_traceSegment_050_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2862 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2862 27 27, g32p_row02_traceSegment_050_2862_0027, g32p_row02_traceSegment_050_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2808 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2808 54 54, g32p_row02_traceSegment_050_2808_0054, g32p_row02_traceSegment_050_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2916 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2916 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2916 13 14, g32p_row02_traceSegment_050_2916_0013, g32p_row02_traceSegment_050_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2943 13 14, g32p_row02_traceSegment_050_2943_0013, g32p_row02_traceSegment_050_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2916 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2916 27 27, g32p_row02_traceSegment_050_2916_0027, g32p_row02_traceSegment_050_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2970 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2970 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2970 13 14, g32p_row02_traceSegment_050_2970_0013, g32p_row02_traceSegment_050_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2997 13 14, g32p_row02_traceSegment_050_2997_0013, g32p_row02_traceSegment_050_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 2970 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2970 27 27, g32p_row02_traceSegment_050_2970_0027, g32p_row02_traceSegment_050_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 2916 108 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2916 54 54, g32p_row02_traceSegment_050_2916_0054, g32p_row02_traceSegment_050_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 2808 216 = [1, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2808 108 108, g32p_row02_traceSegment_050_2808_0108, g32p_row02_traceSegment_050_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 2592 432 = [6, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2592 216 216, g32p_row02_traceSegment_050_2592_0216, g32p_row02_traceSegment_050_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3024 13 14, g32p_row02_traceSegment_050_3024_0013, g32p_row02_traceSegment_050_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3064 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3051 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3051 13 14, g32p_row02_traceSegment_050_3051_0013, g32p_row02_traceSegment_050_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3024 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3024 27 27, g32p_row02_traceSegment_050_3024_0027, g32p_row02_traceSegment_050_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3078 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3078 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3078 13 14, g32p_row02_traceSegment_050_3078_0013, g32p_row02_traceSegment_050_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3105 13 14, g32p_row02_traceSegment_050_3105_0013, g32p_row02_traceSegment_050_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3078 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3078 27 27, g32p_row02_traceSegment_050_3078_0027, g32p_row02_traceSegment_050_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 3024 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3024 54 54, g32p_row02_traceSegment_050_3024_0054, g32p_row02_traceSegment_050_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3132 13 14, g32p_row02_traceSegment_050_3132_0013, g32p_row02_traceSegment_050_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3159 13 14, g32p_row02_traceSegment_050_3159_0013, g32p_row02_traceSegment_050_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3132 27 27, g32p_row02_traceSegment_050_3132_0027, g32p_row02_traceSegment_050_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3186 13 14, g32p_row02_traceSegment_050_3186_0013, g32p_row02_traceSegment_050_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3213 13 14, g32p_row02_traceSegment_050_3213_0013, g32p_row02_traceSegment_050_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3186 27 27, g32p_row02_traceSegment_050_3186_0027, g32p_row02_traceSegment_050_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3132 54 54, g32p_row02_traceSegment_050_3132_0054, g32p_row02_traceSegment_050_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 3024 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3024 108 108, g32p_row02_traceSegment_050_3024_0108, g32p_row02_traceSegment_050_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3240 13 14, g32p_row02_traceSegment_050_3240_0013, g32p_row02_traceSegment_050_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3267 13 14, g32p_row02_traceSegment_050_3267_0013, g32p_row02_traceSegment_050_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3240 27 27, g32p_row02_traceSegment_050_3240_0027, g32p_row02_traceSegment_050_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3294 13 14, g32p_row02_traceSegment_050_3294_0013, g32p_row02_traceSegment_050_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3321 13 14, g32p_row02_traceSegment_050_3321_0013, g32p_row02_traceSegment_050_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3294 27 27, g32p_row02_traceSegment_050_3294_0027, g32p_row02_traceSegment_050_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3240 54 54, g32p_row02_traceSegment_050_3240_0054, g32p_row02_traceSegment_050_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3348 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3361 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3348 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3348 13 14, g32p_row02_traceSegment_050_3348_0013, g32p_row02_traceSegment_050_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3375 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3388 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3375 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3375 13 14, g32p_row02_traceSegment_050_3375_0013, g32p_row02_traceSegment_050_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3348 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3348 27 27, g32p_row02_traceSegment_050_3348_0027, g32p_row02_traceSegment_050_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3415 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3402 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3402 13 14, g32p_row02_traceSegment_050_3402_0013, g32p_row02_traceSegment_050_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_050 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_050 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_050_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_050 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3429 13 14, g32p_row02_traceSegment_050_3429_0013, g32p_row02_traceSegment_050_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_050 3402 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3402 27 27, g32p_row02_traceSegment_050_3402_0027, g32p_row02_traceSegment_050_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_050 3348 108 = [1, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3348 54 54, g32p_row02_traceSegment_050_3348_0054, g32p_row02_traceSegment_050_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_050 3240 216 = [1, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3240 108 108, g32p_row02_traceSegment_050_3240_0108, g32p_row02_traceSegment_050_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_050_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_050 3024 432 = [1, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 3024 216 216, g32p_row02_traceSegment_050_3024_0216, g32p_row02_traceSegment_050_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_050_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_050 2592 864 = [7, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 2592 432 432, g32p_row02_traceSegment_050_2592_0432, g32p_row02_traceSegment_050_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_050_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_050 1728 1728 = [16, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 1728 864 864, g32p_row02_traceSegment_050_1728_0864, g32p_row02_traceSegment_050_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_050_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_050 0 3456 = [32, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_050 0 1728 1728, g32p_row02_traceSegment_050_0000_1728, g32p_row02_traceSegment_050_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 50 = [32, 96] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_050_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_041 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 41) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 41) (g32p_literalTraceValue 1 41)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_041]
  decide +kernel

theorem g32p_row02_tracePolynomial_043 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 43) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 43) (g32p_literalTraceValue 1 43)
      [1, -1, 1] [3456, 3456, 13824, 10368] = true := by
  rw [g32p_row02_traceCoefficients_043]
  decide +kernel

theorem g32p_row02_tracePolynomial_044 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 44) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 44) (g32p_literalTraceValue 1 44)
      [1, -1, 1] [31104, 31104, 31104] = true := by
  rw [g32p_row02_traceCoefficients_044]
  decide +kernel

theorem g32p_row02_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 45) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 45) (g32p_literalTraceValue 1 45)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_045]
  decide +kernel

theorem g32p_row02_tracePolynomial_046 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 46) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 46) (g32p_literalTraceValue 1 46)
      [1, -1, 1] [0, 3456] = true := by
  rw [g32p_row02_traceCoefficients_046]
  decide +kernel

theorem g32p_row02_tracePolynomial_048 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 48) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 48) (g32p_literalTraceValue 1 48)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_048]
  decide +kernel

theorem g32p_row02_tracePolynomial_049 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 49) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 49) (g32p_literalTraceValue 1 49)
      [1, -1, 1] [0, 0, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_049]
  decide +kernel

theorem g32p_row02_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 50) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 50) (g32p_literalTraceValue 1 50)
      [1, -1, 1] [-10368] = true := by
  rw [g32p_row02_traceCoefficients_050]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
