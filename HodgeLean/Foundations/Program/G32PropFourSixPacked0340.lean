import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0339

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_061 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 61 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_061_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 0 13 14, g32p_row04_traceSegment_061_0000_0013, g32p_row04_traceSegment_061_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 27 13 14, g32p_row04_traceSegment_061_0027_0013, g32p_row04_traceSegment_061_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 0 27 27, g32p_row04_traceSegment_061_0000_0027, g32p_row04_traceSegment_061_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 54 13 14, g32p_row04_traceSegment_061_0054_0013, g32p_row04_traceSegment_061_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 81 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 94 14 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 81 27 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 81 13 14, g32p_row04_traceSegment_061_0081_0013, g32p_row04_traceSegment_061_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 54 54 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 54 27 27, g32p_row04_traceSegment_061_0054_0027, g32p_row04_traceSegment_061_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 0 108 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 0 54 54, g32p_row04_traceSegment_061_0000_0054, g32p_row04_traceSegment_061_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 108 13 = [0, 4, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 121 14 = [0, 3, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 108 27 = [0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 108 13 14, g32p_row04_traceSegment_061_0108_0013, g32p_row04_traceSegment_061_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 135 13 14, g32p_row04_traceSegment_061_0135_0013, g32p_row04_traceSegment_061_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 108 54 = [0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 108 27 27, g32p_row04_traceSegment_061_0108_0027, g32p_row04_traceSegment_061_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 162 13 14, g32p_row04_traceSegment_061_0162_0013, g32p_row04_traceSegment_061_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 189 13 14, g32p_row04_traceSegment_061_0189_0013, g32p_row04_traceSegment_061_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 162 27 27, g32p_row04_traceSegment_061_0162_0027, g32p_row04_traceSegment_061_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 108 108 = [0, 7, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 108 54 54, g32p_row04_traceSegment_061_0108_0054, g32p_row04_traceSegment_061_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 0 216 = [0, 9, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 0 108 108, g32p_row04_traceSegment_061_0000_0108, g32p_row04_traceSegment_061_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 216 13 14, g32p_row04_traceSegment_061_0216_0013, g32p_row04_traceSegment_061_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 243 13 14, g32p_row04_traceSegment_061_0243_0013, g32p_row04_traceSegment_061_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 216 27 27, g32p_row04_traceSegment_061_0216_0027, g32p_row04_traceSegment_061_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 270 13 14, g32p_row04_traceSegment_061_0270_0013, g32p_row04_traceSegment_061_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 297 13 14, g32p_row04_traceSegment_061_0297_0013, g32p_row04_traceSegment_061_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 270 27 27, g32p_row04_traceSegment_061_0270_0027, g32p_row04_traceSegment_061_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 216 54 54, g32p_row04_traceSegment_061_0216_0054, g32p_row04_traceSegment_061_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 324 13 14, g32p_row04_traceSegment_061_0324_0013, g32p_row04_traceSegment_061_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 351 13 14, g32p_row04_traceSegment_061_0351_0013, g32p_row04_traceSegment_061_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 324 27 27, g32p_row04_traceSegment_061_0324_0027, g32p_row04_traceSegment_061_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 378 13 14, g32p_row04_traceSegment_061_0378_0013, g32p_row04_traceSegment_061_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 405 13 14, g32p_row04_traceSegment_061_0405_0013, g32p_row04_traceSegment_061_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 378 27 27, g32p_row04_traceSegment_061_0378_0027, g32p_row04_traceSegment_061_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 324 54 54, g32p_row04_traceSegment_061_0324_0054, g32p_row04_traceSegment_061_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 216 108 108, g32p_row04_traceSegment_061_0216_0108, g32p_row04_traceSegment_061_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_061 0 432 = [0, 9, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 0 216 216, g32p_row04_traceSegment_061_0000_0216, g32p_row04_traceSegment_061_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 432 13 14, g32p_row04_traceSegment_061_0432_0013, g32p_row04_traceSegment_061_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 459 13 14, g32p_row04_traceSegment_061_0459_0013, g32p_row04_traceSegment_061_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 432 27 27, g32p_row04_traceSegment_061_0432_0027, g32p_row04_traceSegment_061_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 499 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 486 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 486 13 14, g32p_row04_traceSegment_061_0486_0013, g32p_row04_traceSegment_061_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 513 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 526 14 = [0, 1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 513 27 = [0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 513 13 14, g32p_row04_traceSegment_061_0513_0013, g32p_row04_traceSegment_061_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 486 54 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 486 27 27, g32p_row04_traceSegment_061_0486_0027, g32p_row04_traceSegment_061_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 432 108 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 432 54 54, g32p_row04_traceSegment_061_0432_0054, g32p_row04_traceSegment_061_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 540 13 = [0, 2, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 553 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 540 27 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 540 13 14, g32p_row04_traceSegment_061_0540_0013, g32p_row04_traceSegment_061_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 567 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 580 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 567 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 567 13 14, g32p_row04_traceSegment_061_0567_0013, g32p_row04_traceSegment_061_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 540 54 = [0, 7, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 540 27 27, g32p_row04_traceSegment_061_0540_0027, g32p_row04_traceSegment_061_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 594 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 594 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 594 13 14, g32p_row04_traceSegment_061_0594_0013, g32p_row04_traceSegment_061_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 621 13 14, g32p_row04_traceSegment_061_0621_0013, g32p_row04_traceSegment_061_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 594 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 594 27 27, g32p_row04_traceSegment_061_0594_0027, g32p_row04_traceSegment_061_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 540 108 = [0, 9, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 540 54 54, g32p_row04_traceSegment_061_0540_0054, g32p_row04_traceSegment_061_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 432 216 = [0, 10, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 432 108 108, g32p_row04_traceSegment_061_0432_0108, g32p_row04_traceSegment_061_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 648 13 14, g32p_row04_traceSegment_061_0648_0013, g32p_row04_traceSegment_061_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 675 13 14, g32p_row04_traceSegment_061_0675_0013, g32p_row04_traceSegment_061_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 648 27 27, g32p_row04_traceSegment_061_0648_0027, g32p_row04_traceSegment_061_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 702 13 14, g32p_row04_traceSegment_061_0702_0013, g32p_row04_traceSegment_061_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 729 13 14, g32p_row04_traceSegment_061_0729_0013, g32p_row04_traceSegment_061_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 702 27 27, g32p_row04_traceSegment_061_0702_0027, g32p_row04_traceSegment_061_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 648 54 54, g32p_row04_traceSegment_061_0648_0054, g32p_row04_traceSegment_061_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 769 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 756 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 756 13 14, g32p_row04_traceSegment_061_0756_0013, g32p_row04_traceSegment_061_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 783 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 796 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 783 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 783 13 14, g32p_row04_traceSegment_061_0783_0013, g32p_row04_traceSegment_061_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 756 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 756 27 27, g32p_row04_traceSegment_061_0756_0027, g32p_row04_traceSegment_061_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 810 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 823 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 810 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 810 13 14, g32p_row04_traceSegment_061_0810_0013, g32p_row04_traceSegment_061_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 837 13 14, g32p_row04_traceSegment_061_0837_0013, g32p_row04_traceSegment_061_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 810 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 810 27 27, g32p_row04_traceSegment_061_0810_0027, g32p_row04_traceSegment_061_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 756 108 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 756 54 54, g32p_row04_traceSegment_061_0756_0054, g32p_row04_traceSegment_061_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 648 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 648 108 108, g32p_row04_traceSegment_061_0648_0108, g32p_row04_traceSegment_061_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_061 432 432 = [0, 10, 13] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 432 216 216, g32p_row04_traceSegment_061_0432_0216, g32p_row04_traceSegment_061_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_061 0 864 = [0, 19, 18] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 0 432 432, g32p_row04_traceSegment_061_0000_0432, g32p_row04_traceSegment_061_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 864 13 14, g32p_row04_traceSegment_061_0864_0013, g32p_row04_traceSegment_061_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 891 13 14, g32p_row04_traceSegment_061_0891_0013, g32p_row04_traceSegment_061_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 864 27 27, g32p_row04_traceSegment_061_0864_0027, g32p_row04_traceSegment_061_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 918 13 14, g32p_row04_traceSegment_061_0918_0013, g32p_row04_traceSegment_061_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 945 13 14, g32p_row04_traceSegment_061_0945_0013, g32p_row04_traceSegment_061_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 918 27 27, g32p_row04_traceSegment_061_0918_0027, g32p_row04_traceSegment_061_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 864 54 54, g32p_row04_traceSegment_061_0864_0054, g32p_row04_traceSegment_061_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 972 13 14, g32p_row04_traceSegment_061_0972_0013, g32p_row04_traceSegment_061_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 999 13 14, g32p_row04_traceSegment_061_0999_0013, g32p_row04_traceSegment_061_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 972 27 27, g32p_row04_traceSegment_061_0972_0027, g32p_row04_traceSegment_061_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1026 13 14, g32p_row04_traceSegment_061_1026_0013, g32p_row04_traceSegment_061_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1053 13 14, g32p_row04_traceSegment_061_1053_0013, g32p_row04_traceSegment_061_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1026 27 27, g32p_row04_traceSegment_061_1026_0027, g32p_row04_traceSegment_061_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 972 54 54, g32p_row04_traceSegment_061_0972_0054, g32p_row04_traceSegment_061_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 864 108 108, g32p_row04_traceSegment_061_0864_0108, g32p_row04_traceSegment_061_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1080 13 14, g32p_row04_traceSegment_061_1080_0013, g32p_row04_traceSegment_061_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1107 13 14, g32p_row04_traceSegment_061_1107_0013, g32p_row04_traceSegment_061_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1080 27 27, g32p_row04_traceSegment_061_1080_0027, g32p_row04_traceSegment_061_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1134 13 14, g32p_row04_traceSegment_061_1134_0013, g32p_row04_traceSegment_061_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1161 13 14, g32p_row04_traceSegment_061_1161_0013, g32p_row04_traceSegment_061_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1134 27 27, g32p_row04_traceSegment_061_1134_0027, g32p_row04_traceSegment_061_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1080 54 54, g32p_row04_traceSegment_061_1080_0054, g32p_row04_traceSegment_061_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1188 13 14, g32p_row04_traceSegment_061_1188_0013, g32p_row04_traceSegment_061_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1215 13 14, g32p_row04_traceSegment_061_1215_0013, g32p_row04_traceSegment_061_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1188 27 27, g32p_row04_traceSegment_061_1188_0027, g32p_row04_traceSegment_061_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1242 13 14, g32p_row04_traceSegment_061_1242_0013, g32p_row04_traceSegment_061_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1269 13 14, g32p_row04_traceSegment_061_1269_0013, g32p_row04_traceSegment_061_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1242 27 27, g32p_row04_traceSegment_061_1242_0027, g32p_row04_traceSegment_061_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1188 54 54, g32p_row04_traceSegment_061_1188_0054, g32p_row04_traceSegment_061_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1080 108 108, g32p_row04_traceSegment_061_1080_0108, g32p_row04_traceSegment_061_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_061 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 864 216 216, g32p_row04_traceSegment_061_0864_0216, g32p_row04_traceSegment_061_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1296 13 14, g32p_row04_traceSegment_061_1296_0013, g32p_row04_traceSegment_061_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1323 13 14, g32p_row04_traceSegment_061_1323_0013, g32p_row04_traceSegment_061_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1296 27 27, g32p_row04_traceSegment_061_1296_0027, g32p_row04_traceSegment_061_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1350 13 14, g32p_row04_traceSegment_061_1350_0013, g32p_row04_traceSegment_061_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1377 13 14, g32p_row04_traceSegment_061_1377_0013, g32p_row04_traceSegment_061_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1350 27 27, g32p_row04_traceSegment_061_1350_0027, g32p_row04_traceSegment_061_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1296 54 54, g32p_row04_traceSegment_061_1296_0054, g32p_row04_traceSegment_061_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1404 13 14, g32p_row04_traceSegment_061_1404_0013, g32p_row04_traceSegment_061_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1431 13 14, g32p_row04_traceSegment_061_1431_0013, g32p_row04_traceSegment_061_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1404 27 27, g32p_row04_traceSegment_061_1404_0027, g32p_row04_traceSegment_061_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1458 13 14, g32p_row04_traceSegment_061_1458_0013, g32p_row04_traceSegment_061_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1485 13 14, g32p_row04_traceSegment_061_1485_0013, g32p_row04_traceSegment_061_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1458 27 27, g32p_row04_traceSegment_061_1458_0027, g32p_row04_traceSegment_061_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1404 54 54, g32p_row04_traceSegment_061_1404_0054, g32p_row04_traceSegment_061_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1296 108 108, g32p_row04_traceSegment_061_1296_0108, g32p_row04_traceSegment_061_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1512 13 14, g32p_row04_traceSegment_061_1512_0013, g32p_row04_traceSegment_061_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1539 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1552 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1539 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1539 13 14, g32p_row04_traceSegment_061_1539_0013, g32p_row04_traceSegment_061_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1512 54 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1512 27 27, g32p_row04_traceSegment_061_1512_0027, g32p_row04_traceSegment_061_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1566 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1566 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1566 13 14, g32p_row04_traceSegment_061_1566_0013, g32p_row04_traceSegment_061_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1593 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1606 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1593 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1593 13 14, g32p_row04_traceSegment_061_1593_0013, g32p_row04_traceSegment_061_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1566 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1566 27 27, g32p_row04_traceSegment_061_1566_0027, g32p_row04_traceSegment_061_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 1512 108 = [0, 1, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1512 54 54, g32p_row04_traceSegment_061_1512_0054, g32p_row04_traceSegment_061_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1620 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1633 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1620 27 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1620 13 14, g32p_row04_traceSegment_061_1620_0013, g32p_row04_traceSegment_061_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1647 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1647 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1647 13 14, g32p_row04_traceSegment_061_1647_0013, g32p_row04_traceSegment_061_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1620 54 = [0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1620 27 27, g32p_row04_traceSegment_061_1620_0027, g32p_row04_traceSegment_061_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1674 13 14, g32p_row04_traceSegment_061_1674_0013, g32p_row04_traceSegment_061_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_061 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_061 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_061_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_061 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1701 13 14, g32p_row04_traceSegment_061_1701_0013, g32p_row04_traceSegment_061_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_061 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1674 27 27, g32p_row04_traceSegment_061_1674_0027, g32p_row04_traceSegment_061_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_061 1620 108 = [0, 4, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1620 54 54, g32p_row04_traceSegment_061_1620_0054, g32p_row04_traceSegment_061_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_061 1512 216 = [0, 5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1512 108 108, g32p_row04_traceSegment_061_1512_0108, g32p_row04_traceSegment_061_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_061_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_061 1296 432 = [0, 5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 1296 216 216, g32p_row04_traceSegment_061_1296_0216, g32p_row04_traceSegment_061_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_061 864 864 = [0, 5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 864 432 432, g32p_row04_traceSegment_061_0864_0432, g32p_row04_traceSegment_061_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_061_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_061 0 1728 = [0, 24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_061 0 864 864, g32p_row04_traceSegment_061_0000_0864, g32p_row04_traceSegment_061_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_061 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 61 = [0, 24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_061_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_063 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 63 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_063_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 13 14 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 0 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 0 13 14, g32p_row04_traceSegment_063_0000_0013, g32p_row04_traceSegment_063_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 27 13 14, g32p_row04_traceSegment_063_0027_0013, g32p_row04_traceSegment_063_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 0 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 0 27 27, g32p_row04_traceSegment_063_0000_0027, g32p_row04_traceSegment_063_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 54 13 14, g32p_row04_traceSegment_063_0054_0013, g32p_row04_traceSegment_063_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 81 13 14, g32p_row04_traceSegment_063_0081_0013, g32p_row04_traceSegment_063_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 54 27 27, g32p_row04_traceSegment_063_0054_0027, g32p_row04_traceSegment_063_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 0 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 0 54 54, g32p_row04_traceSegment_063_0000_0054, g32p_row04_traceSegment_063_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 108 13 14, g32p_row04_traceSegment_063_0108_0013, g32p_row04_traceSegment_063_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 135 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 148 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 135 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 135 13 14, g32p_row04_traceSegment_063_0135_0013, g32p_row04_traceSegment_063_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 108 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 108 27 27, g32p_row04_traceSegment_063_0108_0027, g32p_row04_traceSegment_063_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 162 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 162 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 162 13 14, g32p_row04_traceSegment_063_0162_0013, g32p_row04_traceSegment_063_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 189 13 14, g32p_row04_traceSegment_063_0189_0013, g32p_row04_traceSegment_063_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 162 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 162 27 27, g32p_row04_traceSegment_063_0162_0027, g32p_row04_traceSegment_063_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 108 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 108 54 54, g32p_row04_traceSegment_063_0108_0054, g32p_row04_traceSegment_063_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 0 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 0 108 108, g32p_row04_traceSegment_063_0000_0108, g32p_row04_traceSegment_063_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 216 13 14, g32p_row04_traceSegment_063_0216_0013, g32p_row04_traceSegment_063_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 243 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 256 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 243 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 243 13 14, g32p_row04_traceSegment_063_0243_0013, g32p_row04_traceSegment_063_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 216 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 216 27 27, g32p_row04_traceSegment_063_0216_0027, g32p_row04_traceSegment_063_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 270 13 14, g32p_row04_traceSegment_063_0270_0013, g32p_row04_traceSegment_063_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 297 13 14, g32p_row04_traceSegment_063_0297_0013, g32p_row04_traceSegment_063_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 270 27 27, g32p_row04_traceSegment_063_0270_0027, g32p_row04_traceSegment_063_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 216 54 54, g32p_row04_traceSegment_063_0216_0054, g32p_row04_traceSegment_063_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 324 13 14, g32p_row04_traceSegment_063_0324_0013, g32p_row04_traceSegment_063_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 351 13 14, g32p_row04_traceSegment_063_0351_0013, g32p_row04_traceSegment_063_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 324 27 27, g32p_row04_traceSegment_063_0324_0027, g32p_row04_traceSegment_063_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 378 13 14, g32p_row04_traceSegment_063_0378_0013, g32p_row04_traceSegment_063_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 405 13 14, g32p_row04_traceSegment_063_0405_0013, g32p_row04_traceSegment_063_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 378 27 27, g32p_row04_traceSegment_063_0378_0027, g32p_row04_traceSegment_063_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 324 54 54, g32p_row04_traceSegment_063_0324_0054, g32p_row04_traceSegment_063_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 216 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 216 108 108, g32p_row04_traceSegment_063_0216_0108, g32p_row04_traceSegment_063_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_063 0 432 = [10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 0 216 216, g32p_row04_traceSegment_063_0000_0216, g32p_row04_traceSegment_063_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 432 13 14, g32p_row04_traceSegment_063_0432_0013, g32p_row04_traceSegment_063_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 459 13 14, g32p_row04_traceSegment_063_0459_0013, g32p_row04_traceSegment_063_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 432 27 27, g32p_row04_traceSegment_063_0432_0027, g32p_row04_traceSegment_063_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 486 13 14, g32p_row04_traceSegment_063_0486_0013, g32p_row04_traceSegment_063_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 513 13 14, g32p_row04_traceSegment_063_0513_0013, g32p_row04_traceSegment_063_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 486 27 27, g32p_row04_traceSegment_063_0486_0027, g32p_row04_traceSegment_063_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 432 54 54, g32p_row04_traceSegment_063_0432_0054, g32p_row04_traceSegment_063_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 540 13 14, g32p_row04_traceSegment_063_0540_0013, g32p_row04_traceSegment_063_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 567 13 14, g32p_row04_traceSegment_063_0567_0013, g32p_row04_traceSegment_063_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 540 27 27, g32p_row04_traceSegment_063_0540_0027, g32p_row04_traceSegment_063_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 594 13 14, g32p_row04_traceSegment_063_0594_0013, g32p_row04_traceSegment_063_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 621 13 14, g32p_row04_traceSegment_063_0621_0013, g32p_row04_traceSegment_063_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 594 27 27, g32p_row04_traceSegment_063_0594_0027, g32p_row04_traceSegment_063_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 540 54 54, g32p_row04_traceSegment_063_0540_0054, g32p_row04_traceSegment_063_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 432 108 108, g32p_row04_traceSegment_063_0432_0108, g32p_row04_traceSegment_063_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 648 13 14, g32p_row04_traceSegment_063_0648_0013, g32p_row04_traceSegment_063_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 675 13 14, g32p_row04_traceSegment_063_0675_0013, g32p_row04_traceSegment_063_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 648 27 27, g32p_row04_traceSegment_063_0648_0027, g32p_row04_traceSegment_063_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 702 13 14, g32p_row04_traceSegment_063_0702_0013, g32p_row04_traceSegment_063_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 729 13 14, g32p_row04_traceSegment_063_0729_0013, g32p_row04_traceSegment_063_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 702 27 27, g32p_row04_traceSegment_063_0702_0027, g32p_row04_traceSegment_063_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 648 54 54, g32p_row04_traceSegment_063_0648_0054, g32p_row04_traceSegment_063_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 756 13 14, g32p_row04_traceSegment_063_0756_0013, g32p_row04_traceSegment_063_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 783 13 14, g32p_row04_traceSegment_063_0783_0013, g32p_row04_traceSegment_063_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 756 27 27, g32p_row04_traceSegment_063_0756_0027, g32p_row04_traceSegment_063_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 810 13 14, g32p_row04_traceSegment_063_0810_0013, g32p_row04_traceSegment_063_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 850 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 837 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 837 13 14, g32p_row04_traceSegment_063_0837_0013, g32p_row04_traceSegment_063_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 810 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 810 27 27, g32p_row04_traceSegment_063_0810_0027, g32p_row04_traceSegment_063_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 756 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 756 54 54, g32p_row04_traceSegment_063_0756_0054, g32p_row04_traceSegment_063_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 648 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 648 108 108, g32p_row04_traceSegment_063_0648_0108, g32p_row04_traceSegment_063_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_063 432 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 432 216 216, g32p_row04_traceSegment_063_0432_0216, g32p_row04_traceSegment_063_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_063 0 864 = [10, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 0 432 432, g32p_row04_traceSegment_063_0000_0432, g32p_row04_traceSegment_063_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 864 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 864 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 864 13 14, g32p_row04_traceSegment_063_0864_0013, g32p_row04_traceSegment_063_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 891 13 14, g32p_row04_traceSegment_063_0891_0013, g32p_row04_traceSegment_063_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 864 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 864 27 27, g32p_row04_traceSegment_063_0864_0027, g32p_row04_traceSegment_063_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 918 13 14, g32p_row04_traceSegment_063_0918_0013, g32p_row04_traceSegment_063_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 945 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 958 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 945 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 945 13 14, g32p_row04_traceSegment_063_0945_0013, g32p_row04_traceSegment_063_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 918 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 918 27 27, g32p_row04_traceSegment_063_0918_0027, g32p_row04_traceSegment_063_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 864 108 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 864 54 54, g32p_row04_traceSegment_063_0864_0054, g32p_row04_traceSegment_063_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 972 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 985 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 972 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 972 13 14, g32p_row04_traceSegment_063_0972_0013, g32p_row04_traceSegment_063_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 999 13 = [2, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1012 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 999 27 = [3, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 999 13 14, g32p_row04_traceSegment_063_0999_0013, g32p_row04_traceSegment_063_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 972 54 = [6, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 972 27 27, g32p_row04_traceSegment_063_0972_0027, g32p_row04_traceSegment_063_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1039 14 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1026 27 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1026 13 14, g32p_row04_traceSegment_063_1026_0013, g32p_row04_traceSegment_063_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1066 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1053 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1053 13 14, g32p_row04_traceSegment_063_1053_0013, g32p_row04_traceSegment_063_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1026 54 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1026 27 27, g32p_row04_traceSegment_063_1026_0027, g32p_row04_traceSegment_063_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 972 108 = [8, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 972 54 54, g32p_row04_traceSegment_063_0972_0054, g32p_row04_traceSegment_063_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 864 216 = [10, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 864 108 108, g32p_row04_traceSegment_063_0864_0108, g32p_row04_traceSegment_063_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1080 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1080 27 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1080 13 14, g32p_row04_traceSegment_063_1080_0013, g32p_row04_traceSegment_063_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1107 13 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1120 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1107 27 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1107 13 14, g32p_row04_traceSegment_063_1107_0013, g32p_row04_traceSegment_063_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1080 54 = [2, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1080 27 27, g32p_row04_traceSegment_063_1080_0027, g32p_row04_traceSegment_063_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1134 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1147 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1134 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1134 13 14, g32p_row04_traceSegment_063_1134_0013, g32p_row04_traceSegment_063_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1174 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1161 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1161 13 14, g32p_row04_traceSegment_063_1161_0013, g32p_row04_traceSegment_063_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1134 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1134 27 27, g32p_row04_traceSegment_063_1134_0027, g32p_row04_traceSegment_063_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 1080 108 = [2, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1080 54 54, g32p_row04_traceSegment_063_1080_0054, g32p_row04_traceSegment_063_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1188 13 14, g32p_row04_traceSegment_063_1188_0013, g32p_row04_traceSegment_063_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1215 13 14, g32p_row04_traceSegment_063_1215_0013, g32p_row04_traceSegment_063_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1188 27 27, g32p_row04_traceSegment_063_1188_0027, g32p_row04_traceSegment_063_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1242 13 14, g32p_row04_traceSegment_063_1242_0013, g32p_row04_traceSegment_063_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1269 13 14, g32p_row04_traceSegment_063_1269_0013, g32p_row04_traceSegment_063_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1242 27 27, g32p_row04_traceSegment_063_1242_0027, g32p_row04_traceSegment_063_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1188 54 54, g32p_row04_traceSegment_063_1188_0054, g32p_row04_traceSegment_063_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 1080 216 = [2, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1080 108 108, g32p_row04_traceSegment_063_1080_0108, g32p_row04_traceSegment_063_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_063 864 432 = [12, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 864 216 216, g32p_row04_traceSegment_063_0864_0216, g32p_row04_traceSegment_063_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1296 13 14, g32p_row04_traceSegment_063_1296_0013, g32p_row04_traceSegment_063_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1323 13 14, g32p_row04_traceSegment_063_1323_0013, g32p_row04_traceSegment_063_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1296 27 27, g32p_row04_traceSegment_063_1296_0027, g32p_row04_traceSegment_063_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1350 13 14, g32p_row04_traceSegment_063_1350_0013, g32p_row04_traceSegment_063_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1377 13 14, g32p_row04_traceSegment_063_1377_0013, g32p_row04_traceSegment_063_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1350 27 27, g32p_row04_traceSegment_063_1350_0027, g32p_row04_traceSegment_063_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1296 54 54, g32p_row04_traceSegment_063_1296_0054, g32p_row04_traceSegment_063_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1404 13 14, g32p_row04_traceSegment_063_1404_0013, g32p_row04_traceSegment_063_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1431 13 14, g32p_row04_traceSegment_063_1431_0013, g32p_row04_traceSegment_063_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1404 27 27, g32p_row04_traceSegment_063_1404_0027, g32p_row04_traceSegment_063_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1458 13 14, g32p_row04_traceSegment_063_1458_0013, g32p_row04_traceSegment_063_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1485 13 14, g32p_row04_traceSegment_063_1485_0013, g32p_row04_traceSegment_063_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1458 27 27, g32p_row04_traceSegment_063_1458_0027, g32p_row04_traceSegment_063_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1404 54 54, g32p_row04_traceSegment_063_1404_0054, g32p_row04_traceSegment_063_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1296 108 108, g32p_row04_traceSegment_063_1296_0108, g32p_row04_traceSegment_063_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1512 13 14, g32p_row04_traceSegment_063_1512_0013, g32p_row04_traceSegment_063_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1539 13 14, g32p_row04_traceSegment_063_1539_0013, g32p_row04_traceSegment_063_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1512 27 27, g32p_row04_traceSegment_063_1512_0027, g32p_row04_traceSegment_063_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1566 13 14, g32p_row04_traceSegment_063_1566_0013, g32p_row04_traceSegment_063_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1593 13 14, g32p_row04_traceSegment_063_1593_0013, g32p_row04_traceSegment_063_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1566 27 27, g32p_row04_traceSegment_063_1566_0027, g32p_row04_traceSegment_063_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1512 54 54, g32p_row04_traceSegment_063_1512_0054, g32p_row04_traceSegment_063_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1620 13 14, g32p_row04_traceSegment_063_1620_0013, g32p_row04_traceSegment_063_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1647 13 14, g32p_row04_traceSegment_063_1647_0013, g32p_row04_traceSegment_063_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1620 27 27, g32p_row04_traceSegment_063_1620_0027, g32p_row04_traceSegment_063_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1687 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1674 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1674 13 14, g32p_row04_traceSegment_063_1674_0013, g32p_row04_traceSegment_063_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_063 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_063 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_063_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_063 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1701 13 14, g32p_row04_traceSegment_063_1701_0013, g32p_row04_traceSegment_063_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_063 1674 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1674 27 27, g32p_row04_traceSegment_063_1674_0027, g32p_row04_traceSegment_063_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_063 1620 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1620 54 54, g32p_row04_traceSegment_063_1620_0054, g32p_row04_traceSegment_063_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_063 1512 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1512 108 108, g32p_row04_traceSegment_063_1512_0108, g32p_row04_traceSegment_063_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_063_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_063 1296 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 1296 216 216, g32p_row04_traceSegment_063_1296_0216, g32p_row04_traceSegment_063_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_063 864 864 = [14, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 864 432 432, g32p_row04_traceSegment_063_0864_0432, g32p_row04_traceSegment_063_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_063_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_063 0 1728 = [24, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_063 0 864 864, g32p_row04_traceSegment_063_0000_0864, g32p_row04_traceSegment_063_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_063 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 63 = [24, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_063_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_064 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 64 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_064_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 0 13 14, g32p_row04_traceSegment_064_0000_0013, g32p_row04_traceSegment_064_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 27 13 14, g32p_row04_traceSegment_064_0027_0013, g32p_row04_traceSegment_064_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 0 27 27, g32p_row04_traceSegment_064_0000_0027, g32p_row04_traceSegment_064_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 54 13 14, g32p_row04_traceSegment_064_0054_0013, g32p_row04_traceSegment_064_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 81 13 14, g32p_row04_traceSegment_064_0081_0013, g32p_row04_traceSegment_064_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 54 27 27, g32p_row04_traceSegment_064_0054_0027, g32p_row04_traceSegment_064_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 0 54 54, g32p_row04_traceSegment_064_0000_0054, g32p_row04_traceSegment_064_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 108 13 14, g32p_row04_traceSegment_064_0108_0013, g32p_row04_traceSegment_064_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 135 13 14, g32p_row04_traceSegment_064_0135_0013, g32p_row04_traceSegment_064_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 108 27 27, g32p_row04_traceSegment_064_0108_0027, g32p_row04_traceSegment_064_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 162 13 14, g32p_row04_traceSegment_064_0162_0013, g32p_row04_traceSegment_064_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 189 13 14, g32p_row04_traceSegment_064_0189_0013, g32p_row04_traceSegment_064_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 162 27 27, g32p_row04_traceSegment_064_0162_0027, g32p_row04_traceSegment_064_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 108 54 54, g32p_row04_traceSegment_064_0108_0054, g32p_row04_traceSegment_064_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 0 108 108, g32p_row04_traceSegment_064_0000_0108, g32p_row04_traceSegment_064_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 216 13 14, g32p_row04_traceSegment_064_0216_0013, g32p_row04_traceSegment_064_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 243 13 14, g32p_row04_traceSegment_064_0243_0013, g32p_row04_traceSegment_064_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 216 27 27, g32p_row04_traceSegment_064_0216_0027, g32p_row04_traceSegment_064_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 270 13 14, g32p_row04_traceSegment_064_0270_0013, g32p_row04_traceSegment_064_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 297 13 14, g32p_row04_traceSegment_064_0297_0013, g32p_row04_traceSegment_064_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 270 27 27, g32p_row04_traceSegment_064_0270_0027, g32p_row04_traceSegment_064_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 216 54 54, g32p_row04_traceSegment_064_0216_0054, g32p_row04_traceSegment_064_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 324 13 14, g32p_row04_traceSegment_064_0324_0013, g32p_row04_traceSegment_064_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 351 13 14, g32p_row04_traceSegment_064_0351_0013, g32p_row04_traceSegment_064_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 324 27 27, g32p_row04_traceSegment_064_0324_0027, g32p_row04_traceSegment_064_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 378 13 14, g32p_row04_traceSegment_064_0378_0013, g32p_row04_traceSegment_064_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 405 13 14, g32p_row04_traceSegment_064_0405_0013, g32p_row04_traceSegment_064_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 378 27 27, g32p_row04_traceSegment_064_0378_0027, g32p_row04_traceSegment_064_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 324 54 54, g32p_row04_traceSegment_064_0324_0054, g32p_row04_traceSegment_064_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 216 108 108, g32p_row04_traceSegment_064_0216_0108, g32p_row04_traceSegment_064_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_064 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 0 216 216, g32p_row04_traceSegment_064_0000_0216, g32p_row04_traceSegment_064_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 432 13 14, g32p_row04_traceSegment_064_0432_0013, g32p_row04_traceSegment_064_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 459 13 14, g32p_row04_traceSegment_064_0459_0013, g32p_row04_traceSegment_064_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 432 27 27, g32p_row04_traceSegment_064_0432_0027, g32p_row04_traceSegment_064_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 486 13 14, g32p_row04_traceSegment_064_0486_0013, g32p_row04_traceSegment_064_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 513 13 14, g32p_row04_traceSegment_064_0513_0013, g32p_row04_traceSegment_064_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 486 27 27, g32p_row04_traceSegment_064_0486_0027, g32p_row04_traceSegment_064_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 432 54 54, g32p_row04_traceSegment_064_0432_0054, g32p_row04_traceSegment_064_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 540 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 553 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 540 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 540 13 14, g32p_row04_traceSegment_064_0540_0013, g32p_row04_traceSegment_064_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 580 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 567 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 567 13 14, g32p_row04_traceSegment_064_0567_0013, g32p_row04_traceSegment_064_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 540 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 540 27 27, g32p_row04_traceSegment_064_0540_0027, g32p_row04_traceSegment_064_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 594 13 14, g32p_row04_traceSegment_064_0594_0013, g32p_row04_traceSegment_064_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 621 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 621 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 621 13 14, g32p_row04_traceSegment_064_0621_0013, g32p_row04_traceSegment_064_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 594 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 594 27 27, g32p_row04_traceSegment_064_0594_0027, g32p_row04_traceSegment_064_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 540 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 540 54 54, g32p_row04_traceSegment_064_0540_0054, g32p_row04_traceSegment_064_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 432 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 432 108 108, g32p_row04_traceSegment_064_0432_0108, g32p_row04_traceSegment_064_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 648 13 14, g32p_row04_traceSegment_064_0648_0013, g32p_row04_traceSegment_064_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 675 13 14, g32p_row04_traceSegment_064_0675_0013, g32p_row04_traceSegment_064_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 648 27 27, g32p_row04_traceSegment_064_0648_0027, g32p_row04_traceSegment_064_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 702 13 14, g32p_row04_traceSegment_064_0702_0013, g32p_row04_traceSegment_064_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 729 13 14, g32p_row04_traceSegment_064_0729_0013, g32p_row04_traceSegment_064_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 702 27 27, g32p_row04_traceSegment_064_0702_0027, g32p_row04_traceSegment_064_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 648 54 54, g32p_row04_traceSegment_064_0648_0054, g32p_row04_traceSegment_064_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 756 13 14, g32p_row04_traceSegment_064_0756_0013, g32p_row04_traceSegment_064_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 783 13 14, g32p_row04_traceSegment_064_0783_0013, g32p_row04_traceSegment_064_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 756 27 27, g32p_row04_traceSegment_064_0756_0027, g32p_row04_traceSegment_064_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 810 13 14, g32p_row04_traceSegment_064_0810_0013, g32p_row04_traceSegment_064_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 837 13 14, g32p_row04_traceSegment_064_0837_0013, g32p_row04_traceSegment_064_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 810 27 27, g32p_row04_traceSegment_064_0810_0027, g32p_row04_traceSegment_064_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 756 54 54, g32p_row04_traceSegment_064_0756_0054, g32p_row04_traceSegment_064_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 648 108 108, g32p_row04_traceSegment_064_0648_0108, g32p_row04_traceSegment_064_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_064 432 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 432 216 216, g32p_row04_traceSegment_064_0432_0216, g32p_row04_traceSegment_064_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_064 0 864 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 0 432 432, g32p_row04_traceSegment_064_0000_0432, g32p_row04_traceSegment_064_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 864 13 14, g32p_row04_traceSegment_064_0864_0013, g32p_row04_traceSegment_064_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 891 13 14, g32p_row04_traceSegment_064_0891_0013, g32p_row04_traceSegment_064_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 864 27 27, g32p_row04_traceSegment_064_0864_0027, g32p_row04_traceSegment_064_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 918 13 14, g32p_row04_traceSegment_064_0918_0013, g32p_row04_traceSegment_064_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 945 13 14, g32p_row04_traceSegment_064_0945_0013, g32p_row04_traceSegment_064_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 918 27 27, g32p_row04_traceSegment_064_0918_0027, g32p_row04_traceSegment_064_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 864 54 54, g32p_row04_traceSegment_064_0864_0054, g32p_row04_traceSegment_064_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 972 13 14, g32p_row04_traceSegment_064_0972_0013, g32p_row04_traceSegment_064_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 999 13 14, g32p_row04_traceSegment_064_0999_0013, g32p_row04_traceSegment_064_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 972 27 27, g32p_row04_traceSegment_064_0972_0027, g32p_row04_traceSegment_064_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1026 13 14, g32p_row04_traceSegment_064_1026_0013, g32p_row04_traceSegment_064_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1053 13 14, g32p_row04_traceSegment_064_1053_0013, g32p_row04_traceSegment_064_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1026 27 27, g32p_row04_traceSegment_064_1026_0027, g32p_row04_traceSegment_064_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 972 54 54, g32p_row04_traceSegment_064_0972_0054, g32p_row04_traceSegment_064_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 864 108 108, g32p_row04_traceSegment_064_0864_0108, g32p_row04_traceSegment_064_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1080 13 14, g32p_row04_traceSegment_064_1080_0013, g32p_row04_traceSegment_064_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1107 13 14, g32p_row04_traceSegment_064_1107_0013, g32p_row04_traceSegment_064_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1080 27 27, g32p_row04_traceSegment_064_1080_0027, g32p_row04_traceSegment_064_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1134 13 14, g32p_row04_traceSegment_064_1134_0013, g32p_row04_traceSegment_064_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1161 13 14, g32p_row04_traceSegment_064_1161_0013, g32p_row04_traceSegment_064_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1134 27 27, g32p_row04_traceSegment_064_1134_0027, g32p_row04_traceSegment_064_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1080 54 54, g32p_row04_traceSegment_064_1080_0054, g32p_row04_traceSegment_064_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1188 13 14, g32p_row04_traceSegment_064_1188_0013, g32p_row04_traceSegment_064_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1215 13 14, g32p_row04_traceSegment_064_1215_0013, g32p_row04_traceSegment_064_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1188 27 27, g32p_row04_traceSegment_064_1188_0027, g32p_row04_traceSegment_064_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1242 13 14, g32p_row04_traceSegment_064_1242_0013, g32p_row04_traceSegment_064_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1269 13 14, g32p_row04_traceSegment_064_1269_0013, g32p_row04_traceSegment_064_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1242 27 27, g32p_row04_traceSegment_064_1242_0027, g32p_row04_traceSegment_064_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1188 54 54, g32p_row04_traceSegment_064_1188_0054, g32p_row04_traceSegment_064_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1080 108 108, g32p_row04_traceSegment_064_1080_0108, g32p_row04_traceSegment_064_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_064 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 864 216 216, g32p_row04_traceSegment_064_0864_0216, g32p_row04_traceSegment_064_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1296 13 14, g32p_row04_traceSegment_064_1296_0013, g32p_row04_traceSegment_064_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1323 13 14, g32p_row04_traceSegment_064_1323_0013, g32p_row04_traceSegment_064_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1296 27 27, g32p_row04_traceSegment_064_1296_0027, g32p_row04_traceSegment_064_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1350 13 14, g32p_row04_traceSegment_064_1350_0013, g32p_row04_traceSegment_064_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1377 13 14, g32p_row04_traceSegment_064_1377_0013, g32p_row04_traceSegment_064_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1350 27 27, g32p_row04_traceSegment_064_1350_0027, g32p_row04_traceSegment_064_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1296 54 54, g32p_row04_traceSegment_064_1296_0054, g32p_row04_traceSegment_064_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1404 13 14, g32p_row04_traceSegment_064_1404_0013, g32p_row04_traceSegment_064_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1431 13 14, g32p_row04_traceSegment_064_1431_0013, g32p_row04_traceSegment_064_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1404 27 27, g32p_row04_traceSegment_064_1404_0027, g32p_row04_traceSegment_064_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1458 13 14, g32p_row04_traceSegment_064_1458_0013, g32p_row04_traceSegment_064_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1485 13 14, g32p_row04_traceSegment_064_1485_0013, g32p_row04_traceSegment_064_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1458 27 27, g32p_row04_traceSegment_064_1458_0027, g32p_row04_traceSegment_064_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1404 54 54, g32p_row04_traceSegment_064_1404_0054, g32p_row04_traceSegment_064_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1296 108 108, g32p_row04_traceSegment_064_1296_0108, g32p_row04_traceSegment_064_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1512 13 14, g32p_row04_traceSegment_064_1512_0013, g32p_row04_traceSegment_064_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1539 13 14, g32p_row04_traceSegment_064_1539_0013, g32p_row04_traceSegment_064_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1512 27 27, g32p_row04_traceSegment_064_1512_0027, g32p_row04_traceSegment_064_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1579 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1566 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1566 13 14, g32p_row04_traceSegment_064_1566_0013, g32p_row04_traceSegment_064_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1606 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1593 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1593 13 14, g32p_row04_traceSegment_064_1593_0013, g32p_row04_traceSegment_064_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1566 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1566 27 27, g32p_row04_traceSegment_064_1566_0027, g32p_row04_traceSegment_064_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 1512 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1512 54 54, g32p_row04_traceSegment_064_1512_0054, g32p_row04_traceSegment_064_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1620 13 14, g32p_row04_traceSegment_064_1620_0013, g32p_row04_traceSegment_064_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1647 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1647 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1647 13 14, g32p_row04_traceSegment_064_1647_0013, g32p_row04_traceSegment_064_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1620 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1620 27 27, g32p_row04_traceSegment_064_1620_0027, g32p_row04_traceSegment_064_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1674 13 14, g32p_row04_traceSegment_064_1674_0013, g32p_row04_traceSegment_064_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_064 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_064 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_064_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_064 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1701 13 14, g32p_row04_traceSegment_064_1701_0013, g32p_row04_traceSegment_064_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_064 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1674 27 27, g32p_row04_traceSegment_064_1674_0027, g32p_row04_traceSegment_064_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_064 1620 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1620 54 54, g32p_row04_traceSegment_064_1620_0054, g32p_row04_traceSegment_064_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_064 1512 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1512 108 108, g32p_row04_traceSegment_064_1512_0108, g32p_row04_traceSegment_064_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_064_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_064 1296 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 1296 216 216, g32p_row04_traceSegment_064_1296_0216, g32p_row04_traceSegment_064_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_064 864 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 864 432 432, g32p_row04_traceSegment_064_0864_0432, g32p_row04_traceSegment_064_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_064_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_064 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_064 0 864 864, g32p_row04_traceSegment_064_0000_0864, g32p_row04_traceSegment_064_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_064 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 64 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_064_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_065 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 65 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_065_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 0 13 14, g32p_row04_traceSegment_065_0000_0013, g32p_row04_traceSegment_065_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 27 13 14, g32p_row04_traceSegment_065_0027_0013, g32p_row04_traceSegment_065_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 0 27 27, g32p_row04_traceSegment_065_0000_0027, g32p_row04_traceSegment_065_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 54 13 14, g32p_row04_traceSegment_065_0054_0013, g32p_row04_traceSegment_065_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 81 13 14, g32p_row04_traceSegment_065_0081_0013, g32p_row04_traceSegment_065_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 54 27 27, g32p_row04_traceSegment_065_0054_0027, g32p_row04_traceSegment_065_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 0 54 54, g32p_row04_traceSegment_065_0000_0054, g32p_row04_traceSegment_065_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 108 13 14, g32p_row04_traceSegment_065_0108_0013, g32p_row04_traceSegment_065_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 135 13 14, g32p_row04_traceSegment_065_0135_0013, g32p_row04_traceSegment_065_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 108 27 27, g32p_row04_traceSegment_065_0108_0027, g32p_row04_traceSegment_065_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 162 13 14, g32p_row04_traceSegment_065_0162_0013, g32p_row04_traceSegment_065_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 189 13 14, g32p_row04_traceSegment_065_0189_0013, g32p_row04_traceSegment_065_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 162 27 27, g32p_row04_traceSegment_065_0162_0027, g32p_row04_traceSegment_065_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 108 54 54, g32p_row04_traceSegment_065_0108_0054, g32p_row04_traceSegment_065_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 0 108 108, g32p_row04_traceSegment_065_0000_0108, g32p_row04_traceSegment_065_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 216 13 14, g32p_row04_traceSegment_065_0216_0013, g32p_row04_traceSegment_065_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 243 13 14, g32p_row04_traceSegment_065_0243_0013, g32p_row04_traceSegment_065_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 216 27 27, g32p_row04_traceSegment_065_0216_0027, g32p_row04_traceSegment_065_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 270 13 14, g32p_row04_traceSegment_065_0270_0013, g32p_row04_traceSegment_065_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 297 13 14, g32p_row04_traceSegment_065_0297_0013, g32p_row04_traceSegment_065_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 270 27 27, g32p_row04_traceSegment_065_0270_0027, g32p_row04_traceSegment_065_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 216 54 54, g32p_row04_traceSegment_065_0216_0054, g32p_row04_traceSegment_065_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 324 13 14, g32p_row04_traceSegment_065_0324_0013, g32p_row04_traceSegment_065_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 351 13 14, g32p_row04_traceSegment_065_0351_0013, g32p_row04_traceSegment_065_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 324 27 27, g32p_row04_traceSegment_065_0324_0027, g32p_row04_traceSegment_065_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 378 13 14, g32p_row04_traceSegment_065_0378_0013, g32p_row04_traceSegment_065_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 405 13 14, g32p_row04_traceSegment_065_0405_0013, g32p_row04_traceSegment_065_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 378 27 27, g32p_row04_traceSegment_065_0378_0027, g32p_row04_traceSegment_065_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 324 54 54, g32p_row04_traceSegment_065_0324_0054, g32p_row04_traceSegment_065_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 216 108 108, g32p_row04_traceSegment_065_0216_0108, g32p_row04_traceSegment_065_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_065 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 0 216 216, g32p_row04_traceSegment_065_0000_0216, g32p_row04_traceSegment_065_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 432 13 14, g32p_row04_traceSegment_065_0432_0013, g32p_row04_traceSegment_065_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 459 13 14, g32p_row04_traceSegment_065_0459_0013, g32p_row04_traceSegment_065_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 432 27 27, g32p_row04_traceSegment_065_0432_0027, g32p_row04_traceSegment_065_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 486 13 14, g32p_row04_traceSegment_065_0486_0013, g32p_row04_traceSegment_065_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 513 13 14, g32p_row04_traceSegment_065_0513_0013, g32p_row04_traceSegment_065_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 486 27 27, g32p_row04_traceSegment_065_0486_0027, g32p_row04_traceSegment_065_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 432 54 54, g32p_row04_traceSegment_065_0432_0054, g32p_row04_traceSegment_065_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 540 13 14, g32p_row04_traceSegment_065_0540_0013, g32p_row04_traceSegment_065_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 567 13 14, g32p_row04_traceSegment_065_0567_0013, g32p_row04_traceSegment_065_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 540 27 27, g32p_row04_traceSegment_065_0540_0027, g32p_row04_traceSegment_065_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 594 13 14, g32p_row04_traceSegment_065_0594_0013, g32p_row04_traceSegment_065_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 621 13 14, g32p_row04_traceSegment_065_0621_0013, g32p_row04_traceSegment_065_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 594 27 27, g32p_row04_traceSegment_065_0594_0027, g32p_row04_traceSegment_065_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 540 54 54, g32p_row04_traceSegment_065_0540_0054, g32p_row04_traceSegment_065_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 432 108 108, g32p_row04_traceSegment_065_0432_0108, g32p_row04_traceSegment_065_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 648 13 14, g32p_row04_traceSegment_065_0648_0013, g32p_row04_traceSegment_065_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 675 13 14, g32p_row04_traceSegment_065_0675_0013, g32p_row04_traceSegment_065_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 648 27 27, g32p_row04_traceSegment_065_0648_0027, g32p_row04_traceSegment_065_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 702 13 14, g32p_row04_traceSegment_065_0702_0013, g32p_row04_traceSegment_065_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 729 13 14, g32p_row04_traceSegment_065_0729_0013, g32p_row04_traceSegment_065_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 702 27 27, g32p_row04_traceSegment_065_0702_0027, g32p_row04_traceSegment_065_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 648 54 54, g32p_row04_traceSegment_065_0648_0054, g32p_row04_traceSegment_065_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 756 13 14, g32p_row04_traceSegment_065_0756_0013, g32p_row04_traceSegment_065_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 783 13 14, g32p_row04_traceSegment_065_0783_0013, g32p_row04_traceSegment_065_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 756 27 27, g32p_row04_traceSegment_065_0756_0027, g32p_row04_traceSegment_065_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 810 13 14, g32p_row04_traceSegment_065_0810_0013, g32p_row04_traceSegment_065_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 837 13 14, g32p_row04_traceSegment_065_0837_0013, g32p_row04_traceSegment_065_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 810 27 27, g32p_row04_traceSegment_065_0810_0027, g32p_row04_traceSegment_065_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 756 54 54, g32p_row04_traceSegment_065_0756_0054, g32p_row04_traceSegment_065_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 648 108 108, g32p_row04_traceSegment_065_0648_0108, g32p_row04_traceSegment_065_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_065 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 432 216 216, g32p_row04_traceSegment_065_0432_0216, g32p_row04_traceSegment_065_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_065 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 0 432 432, g32p_row04_traceSegment_065_0000_0432, g32p_row04_traceSegment_065_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 864 13 14, g32p_row04_traceSegment_065_0864_0013, g32p_row04_traceSegment_065_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 891 13 14, g32p_row04_traceSegment_065_0891_0013, g32p_row04_traceSegment_065_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 864 27 27, g32p_row04_traceSegment_065_0864_0027, g32p_row04_traceSegment_065_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 918 13 14, g32p_row04_traceSegment_065_0918_0013, g32p_row04_traceSegment_065_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 945 13 14, g32p_row04_traceSegment_065_0945_0013, g32p_row04_traceSegment_065_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 918 27 27, g32p_row04_traceSegment_065_0918_0027, g32p_row04_traceSegment_065_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 864 54 54, g32p_row04_traceSegment_065_0864_0054, g32p_row04_traceSegment_065_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 972 13 14, g32p_row04_traceSegment_065_0972_0013, g32p_row04_traceSegment_065_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 999 13 14, g32p_row04_traceSegment_065_0999_0013, g32p_row04_traceSegment_065_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 972 27 27, g32p_row04_traceSegment_065_0972_0027, g32p_row04_traceSegment_065_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1026 13 14, g32p_row04_traceSegment_065_1026_0013, g32p_row04_traceSegment_065_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1053 13 14, g32p_row04_traceSegment_065_1053_0013, g32p_row04_traceSegment_065_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1026 27 27, g32p_row04_traceSegment_065_1026_0027, g32p_row04_traceSegment_065_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 972 54 54, g32p_row04_traceSegment_065_0972_0054, g32p_row04_traceSegment_065_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 864 108 108, g32p_row04_traceSegment_065_0864_0108, g32p_row04_traceSegment_065_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1080 13 14, g32p_row04_traceSegment_065_1080_0013, g32p_row04_traceSegment_065_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1107 13 14, g32p_row04_traceSegment_065_1107_0013, g32p_row04_traceSegment_065_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1080 27 27, g32p_row04_traceSegment_065_1080_0027, g32p_row04_traceSegment_065_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1134 13 14, g32p_row04_traceSegment_065_1134_0013, g32p_row04_traceSegment_065_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1161 13 14, g32p_row04_traceSegment_065_1161_0013, g32p_row04_traceSegment_065_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1134 27 27, g32p_row04_traceSegment_065_1134_0027, g32p_row04_traceSegment_065_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1080 54 54, g32p_row04_traceSegment_065_1080_0054, g32p_row04_traceSegment_065_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1188 13 14, g32p_row04_traceSegment_065_1188_0013, g32p_row04_traceSegment_065_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1228 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1215 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1215 13 14, g32p_row04_traceSegment_065_1215_0013, g32p_row04_traceSegment_065_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1188 27 27, g32p_row04_traceSegment_065_1188_0027, g32p_row04_traceSegment_065_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1242 13 14, g32p_row04_traceSegment_065_1242_0013, g32p_row04_traceSegment_065_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1269 13 14, g32p_row04_traceSegment_065_1269_0013, g32p_row04_traceSegment_065_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1242 27 27, g32p_row04_traceSegment_065_1242_0027, g32p_row04_traceSegment_065_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1188 54 54, g32p_row04_traceSegment_065_1188_0054, g32p_row04_traceSegment_065_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1080 108 108, g32p_row04_traceSegment_065_1080_0108, g32p_row04_traceSegment_065_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_065 864 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 864 216 216, g32p_row04_traceSegment_065_0864_0216, g32p_row04_traceSegment_065_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1296 13 14, g32p_row04_traceSegment_065_1296_0013, g32p_row04_traceSegment_065_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1323 13 14, g32p_row04_traceSegment_065_1323_0013, g32p_row04_traceSegment_065_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1296 27 27, g32p_row04_traceSegment_065_1296_0027, g32p_row04_traceSegment_065_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1350 13 14, g32p_row04_traceSegment_065_1350_0013, g32p_row04_traceSegment_065_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1377 13 14, g32p_row04_traceSegment_065_1377_0013, g32p_row04_traceSegment_065_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1350 27 27, g32p_row04_traceSegment_065_1350_0027, g32p_row04_traceSegment_065_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1296 54 54, g32p_row04_traceSegment_065_1296_0054, g32p_row04_traceSegment_065_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1417 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1404 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1404 13 14, g32p_row04_traceSegment_065_1404_0013, g32p_row04_traceSegment_065_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1431 13 14, g32p_row04_traceSegment_065_1431_0013, g32p_row04_traceSegment_065_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1404 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1404 27 27, g32p_row04_traceSegment_065_1404_0027, g32p_row04_traceSegment_065_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1458 13 14, g32p_row04_traceSegment_065_1458_0013, g32p_row04_traceSegment_065_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1485 13 14, g32p_row04_traceSegment_065_1485_0013, g32p_row04_traceSegment_065_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1458 27 27, g32p_row04_traceSegment_065_1458_0027, g32p_row04_traceSegment_065_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 1404 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1404 54 54, g32p_row04_traceSegment_065_1404_0054, g32p_row04_traceSegment_065_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 1296 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1296 108 108, g32p_row04_traceSegment_065_1296_0108, g32p_row04_traceSegment_065_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1512 13 14, g32p_row04_traceSegment_065_1512_0013, g32p_row04_traceSegment_065_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1539 13 14, g32p_row04_traceSegment_065_1539_0013, g32p_row04_traceSegment_065_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1512 27 27, g32p_row04_traceSegment_065_1512_0027, g32p_row04_traceSegment_065_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1566 13 14, g32p_row04_traceSegment_065_1566_0013, g32p_row04_traceSegment_065_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1593 13 14, g32p_row04_traceSegment_065_1593_0013, g32p_row04_traceSegment_065_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1566 27 27, g32p_row04_traceSegment_065_1566_0027, g32p_row04_traceSegment_065_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1512 54 54, g32p_row04_traceSegment_065_1512_0054, g32p_row04_traceSegment_065_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1620 13 14, g32p_row04_traceSegment_065_1620_0013, g32p_row04_traceSegment_065_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1647 13 14, g32p_row04_traceSegment_065_1647_0013, g32p_row04_traceSegment_065_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1620 27 27, g32p_row04_traceSegment_065_1620_0027, g32p_row04_traceSegment_065_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1674 13 14, g32p_row04_traceSegment_065_1674_0013, g32p_row04_traceSegment_065_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_065 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_065 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_065_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_065 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1701 13 14, g32p_row04_traceSegment_065_1701_0013, g32p_row04_traceSegment_065_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_065 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1674 27 27, g32p_row04_traceSegment_065_1674_0027, g32p_row04_traceSegment_065_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_065 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1620 54 54, g32p_row04_traceSegment_065_1620_0054, g32p_row04_traceSegment_065_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_065 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1512 108 108, g32p_row04_traceSegment_065_1512_0108, g32p_row04_traceSegment_065_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_065_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_065 1296 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 1296 216 216, g32p_row04_traceSegment_065_1296_0216, g32p_row04_traceSegment_065_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_065 864 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 864 432 432, g32p_row04_traceSegment_065_0864_0432, g32p_row04_traceSegment_065_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_065_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_065 0 1728 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_065 0 864 864, g32p_row04_traceSegment_065_0000_0864, g32p_row04_traceSegment_065_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_065 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 65 = [0, 0, 2] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_065_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_066 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 66 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_066_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 0 13 14, g32p_row04_traceSegment_066_0000_0013, g32p_row04_traceSegment_066_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 27 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 27 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 27 13 14, g32p_row04_traceSegment_066_0027_0013, g32p_row04_traceSegment_066_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 0 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 0 27 27, g32p_row04_traceSegment_066_0000_0027, g32p_row04_traceSegment_066_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 54 13 14, g32p_row04_traceSegment_066_0054_0013, g32p_row04_traceSegment_066_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 81 13 14, g32p_row04_traceSegment_066_0081_0013, g32p_row04_traceSegment_066_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 54 27 27, g32p_row04_traceSegment_066_0054_0027, g32p_row04_traceSegment_066_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 0 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 0 54 54, g32p_row04_traceSegment_066_0000_0054, g32p_row04_traceSegment_066_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 108 13 14, g32p_row04_traceSegment_066_0108_0013, g32p_row04_traceSegment_066_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 135 13 14, g32p_row04_traceSegment_066_0135_0013, g32p_row04_traceSegment_066_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 108 27 27, g32p_row04_traceSegment_066_0108_0027, g32p_row04_traceSegment_066_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 162 13 14, g32p_row04_traceSegment_066_0162_0013, g32p_row04_traceSegment_066_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 189 13 14, g32p_row04_traceSegment_066_0189_0013, g32p_row04_traceSegment_066_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 162 27 27, g32p_row04_traceSegment_066_0162_0027, g32p_row04_traceSegment_066_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 108 54 54, g32p_row04_traceSegment_066_0108_0054, g32p_row04_traceSegment_066_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 0 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 0 108 108, g32p_row04_traceSegment_066_0000_0108, g32p_row04_traceSegment_066_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 216 13 14, g32p_row04_traceSegment_066_0216_0013, g32p_row04_traceSegment_066_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 243 13 14, g32p_row04_traceSegment_066_0243_0013, g32p_row04_traceSegment_066_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 216 27 27, g32p_row04_traceSegment_066_0216_0027, g32p_row04_traceSegment_066_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 270 13 14, g32p_row04_traceSegment_066_0270_0013, g32p_row04_traceSegment_066_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 297 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 310 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 297 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 297 13 14, g32p_row04_traceSegment_066_0297_0013, g32p_row04_traceSegment_066_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 270 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 270 27 27, g32p_row04_traceSegment_066_0270_0027, g32p_row04_traceSegment_066_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 216 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 216 54 54, g32p_row04_traceSegment_066_0216_0054, g32p_row04_traceSegment_066_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 324 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 337 14 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 324 27 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 324 13 14, g32p_row04_traceSegment_066_0324_0013, g32p_row04_traceSegment_066_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 351 13 = [1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 364 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 351 27 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 351 13 14, g32p_row04_traceSegment_066_0351_0013, g32p_row04_traceSegment_066_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 324 54 = [2, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 324 27 27, g32p_row04_traceSegment_066_0324_0027, g32p_row04_traceSegment_066_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 391 14 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 378 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 378 13 14, g32p_row04_traceSegment_066_0378_0013, g32p_row04_traceSegment_066_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 405 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 418 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 405 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 405 13 14, g32p_row04_traceSegment_066_0405_0013, g32p_row04_traceSegment_066_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 378 54 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 378 27 27, g32p_row04_traceSegment_066_0378_0027, g32p_row04_traceSegment_066_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 324 108 = [5, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 324 54 54, g32p_row04_traceSegment_066_0324_0054, g32p_row04_traceSegment_066_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 216 216 = [5, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 216 108 108, g32p_row04_traceSegment_066_0216_0108, g32p_row04_traceSegment_066_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_066 0 432 = [5, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 0 216 216, g32p_row04_traceSegment_066_0000_0216, g32p_row04_traceSegment_066_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 432 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 445 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 432 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 432 13 14, g32p_row04_traceSegment_066_0432_0013, g32p_row04_traceSegment_066_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 459 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 459 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 459 13 14, g32p_row04_traceSegment_066_0459_0013, g32p_row04_traceSegment_066_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 432 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 432 27 27, g32p_row04_traceSegment_066_0432_0027, g32p_row04_traceSegment_066_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 486 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 486 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 486 13 14, g32p_row04_traceSegment_066_0486_0013, g32p_row04_traceSegment_066_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 513 13 14, g32p_row04_traceSegment_066_0513_0013, g32p_row04_traceSegment_066_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 486 27 27, g32p_row04_traceSegment_066_0486_0027, g32p_row04_traceSegment_066_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 432 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 432 54 54, g32p_row04_traceSegment_066_0432_0054, g32p_row04_traceSegment_066_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 540 13 14, g32p_row04_traceSegment_066_0540_0013, g32p_row04_traceSegment_066_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 567 13 14, g32p_row04_traceSegment_066_0567_0013, g32p_row04_traceSegment_066_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 540 27 27, g32p_row04_traceSegment_066_0540_0027, g32p_row04_traceSegment_066_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 594 13 14, g32p_row04_traceSegment_066_0594_0013, g32p_row04_traceSegment_066_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 621 13 14, g32p_row04_traceSegment_066_0621_0013, g32p_row04_traceSegment_066_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 594 27 27, g32p_row04_traceSegment_066_0594_0027, g32p_row04_traceSegment_066_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 540 54 54, g32p_row04_traceSegment_066_0540_0054, g32p_row04_traceSegment_066_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 432 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 432 108 108, g32p_row04_traceSegment_066_0432_0108, g32p_row04_traceSegment_066_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 648 13 14, g32p_row04_traceSegment_066_0648_0013, g32p_row04_traceSegment_066_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 675 13 14, g32p_row04_traceSegment_066_0675_0013, g32p_row04_traceSegment_066_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 648 27 27, g32p_row04_traceSegment_066_0648_0027, g32p_row04_traceSegment_066_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 702 13 14, g32p_row04_traceSegment_066_0702_0013, g32p_row04_traceSegment_066_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 729 13 14, g32p_row04_traceSegment_066_0729_0013, g32p_row04_traceSegment_066_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 702 27 27, g32p_row04_traceSegment_066_0702_0027, g32p_row04_traceSegment_066_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 648 54 54, g32p_row04_traceSegment_066_0648_0054, g32p_row04_traceSegment_066_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 756 13 14, g32p_row04_traceSegment_066_0756_0013, g32p_row04_traceSegment_066_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 783 13 14, g32p_row04_traceSegment_066_0783_0013, g32p_row04_traceSegment_066_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 756 27 27, g32p_row04_traceSegment_066_0756_0027, g32p_row04_traceSegment_066_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 810 13 14, g32p_row04_traceSegment_066_0810_0013, g32p_row04_traceSegment_066_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 837 13 14, g32p_row04_traceSegment_066_0837_0013, g32p_row04_traceSegment_066_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 810 27 27, g32p_row04_traceSegment_066_0810_0027, g32p_row04_traceSegment_066_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 756 54 54, g32p_row04_traceSegment_066_0756_0054, g32p_row04_traceSegment_066_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 648 108 108, g32p_row04_traceSegment_066_0648_0108, g32p_row04_traceSegment_066_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_066 432 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 432 216 216, g32p_row04_traceSegment_066_0432_0216, g32p_row04_traceSegment_066_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_066 0 864 = [11, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 0 432 432, g32p_row04_traceSegment_066_0000_0432, g32p_row04_traceSegment_066_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 864 13 14, g32p_row04_traceSegment_066_0864_0013, g32p_row04_traceSegment_066_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 891 13 14, g32p_row04_traceSegment_066_0891_0013, g32p_row04_traceSegment_066_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 864 27 27, g32p_row04_traceSegment_066_0864_0027, g32p_row04_traceSegment_066_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 918 13 14, g32p_row04_traceSegment_066_0918_0013, g32p_row04_traceSegment_066_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 945 13 14, g32p_row04_traceSegment_066_0945_0013, g32p_row04_traceSegment_066_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 918 27 27, g32p_row04_traceSegment_066_0918_0027, g32p_row04_traceSegment_066_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 864 54 54, g32p_row04_traceSegment_066_0864_0054, g32p_row04_traceSegment_066_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 972 13 14, g32p_row04_traceSegment_066_0972_0013, g32p_row04_traceSegment_066_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 999 13 14, g32p_row04_traceSegment_066_0999_0013, g32p_row04_traceSegment_066_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 972 27 27, g32p_row04_traceSegment_066_0972_0027, g32p_row04_traceSegment_066_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1026 13 14, g32p_row04_traceSegment_066_1026_0013, g32p_row04_traceSegment_066_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1053 13 14, g32p_row04_traceSegment_066_1053_0013, g32p_row04_traceSegment_066_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1026 27 27, g32p_row04_traceSegment_066_1026_0027, g32p_row04_traceSegment_066_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 972 54 54, g32p_row04_traceSegment_066_0972_0054, g32p_row04_traceSegment_066_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 864 108 108, g32p_row04_traceSegment_066_0864_0108, g32p_row04_traceSegment_066_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1080 13 14, g32p_row04_traceSegment_066_1080_0013, g32p_row04_traceSegment_066_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1107 13 14, g32p_row04_traceSegment_066_1107_0013, g32p_row04_traceSegment_066_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1080 27 27, g32p_row04_traceSegment_066_1080_0027, g32p_row04_traceSegment_066_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1134 13 14, g32p_row04_traceSegment_066_1134_0013, g32p_row04_traceSegment_066_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1161 13 14, g32p_row04_traceSegment_066_1161_0013, g32p_row04_traceSegment_066_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1134 27 27, g32p_row04_traceSegment_066_1134_0027, g32p_row04_traceSegment_066_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1080 54 54, g32p_row04_traceSegment_066_1080_0054, g32p_row04_traceSegment_066_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1188 13 14, g32p_row04_traceSegment_066_1188_0013, g32p_row04_traceSegment_066_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1215 13 14, g32p_row04_traceSegment_066_1215_0013, g32p_row04_traceSegment_066_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1188 27 27, g32p_row04_traceSegment_066_1188_0027, g32p_row04_traceSegment_066_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1242 13 14, g32p_row04_traceSegment_066_1242_0013, g32p_row04_traceSegment_066_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1282 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1269 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1269 13 14, g32p_row04_traceSegment_066_1269_0013, g32p_row04_traceSegment_066_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1242 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1242 27 27, g32p_row04_traceSegment_066_1242_0027, g32p_row04_traceSegment_066_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 1188 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1188 54 54, g32p_row04_traceSegment_066_1188_0054, g32p_row04_traceSegment_066_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 1080 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1080 108 108, g32p_row04_traceSegment_066_1080_0108, g32p_row04_traceSegment_066_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_066 864 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 864 216 216, g32p_row04_traceSegment_066_0864_0216, g32p_row04_traceSegment_066_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1296 13 14, g32p_row04_traceSegment_066_1296_0013, g32p_row04_traceSegment_066_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1323 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1323 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1323 13 14, g32p_row04_traceSegment_066_1323_0013, g32p_row04_traceSegment_066_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1296 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1296 27 27, g32p_row04_traceSegment_066_1296_0027, g32p_row04_traceSegment_066_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1363 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1350 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1350 13 14, g32p_row04_traceSegment_066_1350_0013, g32p_row04_traceSegment_066_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1377 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1377 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1377 13 14, g32p_row04_traceSegment_066_1377_0013, g32p_row04_traceSegment_066_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1350 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1350 27 27, g32p_row04_traceSegment_066_1350_0027, g32p_row04_traceSegment_066_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 1296 108 = [3, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1296 54 54, g32p_row04_traceSegment_066_1296_0054, g32p_row04_traceSegment_066_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1404 13 14, g32p_row04_traceSegment_066_1404_0013, g32p_row04_traceSegment_066_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1444 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1431 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1431 13 14, g32p_row04_traceSegment_066_1431_0013, g32p_row04_traceSegment_066_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1404 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1404 27 27, g32p_row04_traceSegment_066_1404_0027, g32p_row04_traceSegment_066_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1458 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1458 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1458 13 14, g32p_row04_traceSegment_066_1458_0013, g32p_row04_traceSegment_066_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1485 13 14, g32p_row04_traceSegment_066_1485_0013, g32p_row04_traceSegment_066_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1458 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1458 27 27, g32p_row04_traceSegment_066_1458_0027, g32p_row04_traceSegment_066_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 1404 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1404 54 54, g32p_row04_traceSegment_066_1404_0054, g32p_row04_traceSegment_066_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 1296 216 = [3, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1296 108 108, g32p_row04_traceSegment_066_1296_0108, g32p_row04_traceSegment_066_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1512 13 14, g32p_row04_traceSegment_066_1512_0013, g32p_row04_traceSegment_066_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1539 13 14, g32p_row04_traceSegment_066_1539_0013, g32p_row04_traceSegment_066_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1512 27 27, g32p_row04_traceSegment_066_1512_0027, g32p_row04_traceSegment_066_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1566 13 14, g32p_row04_traceSegment_066_1566_0013, g32p_row04_traceSegment_066_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1593 13 14, g32p_row04_traceSegment_066_1593_0013, g32p_row04_traceSegment_066_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1566 27 27, g32p_row04_traceSegment_066_1566_0027, g32p_row04_traceSegment_066_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1512 54 54, g32p_row04_traceSegment_066_1512_0054, g32p_row04_traceSegment_066_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1620 13 14, g32p_row04_traceSegment_066_1620_0013, g32p_row04_traceSegment_066_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1647 13 14, g32p_row04_traceSegment_066_1647_0013, g32p_row04_traceSegment_066_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1620 27 27, g32p_row04_traceSegment_066_1620_0027, g32p_row04_traceSegment_066_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1674 13 14, g32p_row04_traceSegment_066_1674_0013, g32p_row04_traceSegment_066_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_066 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_066 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_066_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_066 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1701 13 14, g32p_row04_traceSegment_066_1701_0013, g32p_row04_traceSegment_066_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_066 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1674 27 27, g32p_row04_traceSegment_066_1674_0027, g32p_row04_traceSegment_066_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_066 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1620 54 54, g32p_row04_traceSegment_066_1620_0054, g32p_row04_traceSegment_066_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_066 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1512 108 108, g32p_row04_traceSegment_066_1512_0108, g32p_row04_traceSegment_066_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_066_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_066 1296 432 = [3, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 1296 216 216, g32p_row04_traceSegment_066_1296_0216, g32p_row04_traceSegment_066_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_066 864 864 = [5, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 864 432 432, g32p_row04_traceSegment_066_0864_0432, g32p_row04_traceSegment_066_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_066_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_066 0 1728 = [16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_066 0 864 864, g32p_row04_traceSegment_066_0000_0864, g32p_row04_traceSegment_066_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_066 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 66 = [16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_066_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_067 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 67 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_067_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 0 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 0 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 0 13 14, g32p_row04_traceSegment_067_0000_0013, g32p_row04_traceSegment_067_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 27 13 14, g32p_row04_traceSegment_067_0027_0013, g32p_row04_traceSegment_067_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 0 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 0 27 27, g32p_row04_traceSegment_067_0000_0027, g32p_row04_traceSegment_067_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 54 13 14, g32p_row04_traceSegment_067_0054_0013, g32p_row04_traceSegment_067_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 81 13 14, g32p_row04_traceSegment_067_0081_0013, g32p_row04_traceSegment_067_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 54 27 27, g32p_row04_traceSegment_067_0054_0027, g32p_row04_traceSegment_067_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 0 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 0 54 54, g32p_row04_traceSegment_067_0000_0054, g32p_row04_traceSegment_067_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 108 13 14, g32p_row04_traceSegment_067_0108_0013, g32p_row04_traceSegment_067_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 135 13 14, g32p_row04_traceSegment_067_0135_0013, g32p_row04_traceSegment_067_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 108 27 27, g32p_row04_traceSegment_067_0108_0027, g32p_row04_traceSegment_067_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 162 13 14, g32p_row04_traceSegment_067_0162_0013, g32p_row04_traceSegment_067_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 189 13 14, g32p_row04_traceSegment_067_0189_0013, g32p_row04_traceSegment_067_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 162 27 27, g32p_row04_traceSegment_067_0162_0027, g32p_row04_traceSegment_067_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 108 54 54, g32p_row04_traceSegment_067_0108_0054, g32p_row04_traceSegment_067_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 0 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 0 108 108, g32p_row04_traceSegment_067_0000_0108, g32p_row04_traceSegment_067_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 216 13 14, g32p_row04_traceSegment_067_0216_0013, g32p_row04_traceSegment_067_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 243 13 14, g32p_row04_traceSegment_067_0243_0013, g32p_row04_traceSegment_067_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 216 27 27, g32p_row04_traceSegment_067_0216_0027, g32p_row04_traceSegment_067_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 270 13 14, g32p_row04_traceSegment_067_0270_0013, g32p_row04_traceSegment_067_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 297 13 14, g32p_row04_traceSegment_067_0297_0013, g32p_row04_traceSegment_067_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 270 27 27, g32p_row04_traceSegment_067_0270_0027, g32p_row04_traceSegment_067_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 216 54 54, g32p_row04_traceSegment_067_0216_0054, g32p_row04_traceSegment_067_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 324 13 14, g32p_row04_traceSegment_067_0324_0013, g32p_row04_traceSegment_067_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 351 13 14, g32p_row04_traceSegment_067_0351_0013, g32p_row04_traceSegment_067_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 324 27 27, g32p_row04_traceSegment_067_0324_0027, g32p_row04_traceSegment_067_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 378 13 14, g32p_row04_traceSegment_067_0378_0013, g32p_row04_traceSegment_067_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 405 13 14, g32p_row04_traceSegment_067_0405_0013, g32p_row04_traceSegment_067_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 378 27 27, g32p_row04_traceSegment_067_0378_0027, g32p_row04_traceSegment_067_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 324 54 54, g32p_row04_traceSegment_067_0324_0054, g32p_row04_traceSegment_067_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 216 108 108, g32p_row04_traceSegment_067_0216_0108, g32p_row04_traceSegment_067_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_067 0 432 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 0 216 216, g32p_row04_traceSegment_067_0000_0216, g32p_row04_traceSegment_067_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 432 13 14, g32p_row04_traceSegment_067_0432_0013, g32p_row04_traceSegment_067_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 459 13 14, g32p_row04_traceSegment_067_0459_0013, g32p_row04_traceSegment_067_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 432 27 27, g32p_row04_traceSegment_067_0432_0027, g32p_row04_traceSegment_067_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 486 13 14, g32p_row04_traceSegment_067_0486_0013, g32p_row04_traceSegment_067_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 513 13 14, g32p_row04_traceSegment_067_0513_0013, g32p_row04_traceSegment_067_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 486 27 27, g32p_row04_traceSegment_067_0486_0027, g32p_row04_traceSegment_067_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 432 54 54, g32p_row04_traceSegment_067_0432_0054, g32p_row04_traceSegment_067_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 540 13 14, g32p_row04_traceSegment_067_0540_0013, g32p_row04_traceSegment_067_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 567 13 14, g32p_row04_traceSegment_067_0567_0013, g32p_row04_traceSegment_067_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 540 27 27, g32p_row04_traceSegment_067_0540_0027, g32p_row04_traceSegment_067_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 607 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 594 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 594 13 14, g32p_row04_traceSegment_067_0594_0013, g32p_row04_traceSegment_067_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 621 13 14, g32p_row04_traceSegment_067_0621_0013, g32p_row04_traceSegment_067_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 594 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 594 27 27, g32p_row04_traceSegment_067_0594_0027, g32p_row04_traceSegment_067_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 540 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 540 54 54, g32p_row04_traceSegment_067_0540_0054, g32p_row04_traceSegment_067_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 432 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 432 108 108, g32p_row04_traceSegment_067_0432_0108, g32p_row04_traceSegment_067_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 648 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 648 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 648 13 14, g32p_row04_traceSegment_067_0648_0013, g32p_row04_traceSegment_067_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 675 13 14, g32p_row04_traceSegment_067_0675_0013, g32p_row04_traceSegment_067_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 648 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 648 27 27, g32p_row04_traceSegment_067_0648_0027, g32p_row04_traceSegment_067_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 715 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 702 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 702 13 14, g32p_row04_traceSegment_067_0702_0013, g32p_row04_traceSegment_067_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 729 13 14, g32p_row04_traceSegment_067_0729_0013, g32p_row04_traceSegment_067_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 702 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 702 27 27, g32p_row04_traceSegment_067_0702_0027, g32p_row04_traceSegment_067_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 648 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 648 54 54, g32p_row04_traceSegment_067_0648_0054, g32p_row04_traceSegment_067_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 756 13 14, g32p_row04_traceSegment_067_0756_0013, g32p_row04_traceSegment_067_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 783 13 14, g32p_row04_traceSegment_067_0783_0013, g32p_row04_traceSegment_067_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 756 27 27, g32p_row04_traceSegment_067_0756_0027, g32p_row04_traceSegment_067_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 810 13 14, g32p_row04_traceSegment_067_0810_0013, g32p_row04_traceSegment_067_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 837 13 14, g32p_row04_traceSegment_067_0837_0013, g32p_row04_traceSegment_067_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 810 27 27, g32p_row04_traceSegment_067_0810_0027, g32p_row04_traceSegment_067_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 756 54 54, g32p_row04_traceSegment_067_0756_0054, g32p_row04_traceSegment_067_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 648 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 648 108 108, g32p_row04_traceSegment_067_0648_0108, g32p_row04_traceSegment_067_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_067 432 432 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 432 216 216, g32p_row04_traceSegment_067_0432_0216, g32p_row04_traceSegment_067_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_067 0 864 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 0 432 432, g32p_row04_traceSegment_067_0000_0432, g32p_row04_traceSegment_067_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 864 13 14, g32p_row04_traceSegment_067_0864_0013, g32p_row04_traceSegment_067_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 891 13 14, g32p_row04_traceSegment_067_0891_0013, g32p_row04_traceSegment_067_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 864 27 27, g32p_row04_traceSegment_067_0864_0027, g32p_row04_traceSegment_067_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 918 13 14, g32p_row04_traceSegment_067_0918_0013, g32p_row04_traceSegment_067_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 945 13 14, g32p_row04_traceSegment_067_0945_0013, g32p_row04_traceSegment_067_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 918 27 27, g32p_row04_traceSegment_067_0918_0027, g32p_row04_traceSegment_067_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 864 54 54, g32p_row04_traceSegment_067_0864_0054, g32p_row04_traceSegment_067_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 972 13 14, g32p_row04_traceSegment_067_0972_0013, g32p_row04_traceSegment_067_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 999 13 14, g32p_row04_traceSegment_067_0999_0013, g32p_row04_traceSegment_067_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 972 27 27, g32p_row04_traceSegment_067_0972_0027, g32p_row04_traceSegment_067_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1026 13 14, g32p_row04_traceSegment_067_1026_0013, g32p_row04_traceSegment_067_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1053 13 14, g32p_row04_traceSegment_067_1053_0013, g32p_row04_traceSegment_067_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1026 27 27, g32p_row04_traceSegment_067_1026_0027, g32p_row04_traceSegment_067_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 972 54 54, g32p_row04_traceSegment_067_0972_0054, g32p_row04_traceSegment_067_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 864 108 108, g32p_row04_traceSegment_067_0864_0108, g32p_row04_traceSegment_067_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1080 13 14, g32p_row04_traceSegment_067_1080_0013, g32p_row04_traceSegment_067_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1107 13 14, g32p_row04_traceSegment_067_1107_0013, g32p_row04_traceSegment_067_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1080 27 27, g32p_row04_traceSegment_067_1080_0027, g32p_row04_traceSegment_067_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1134 13 14, g32p_row04_traceSegment_067_1134_0013, g32p_row04_traceSegment_067_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1161 13 14, g32p_row04_traceSegment_067_1161_0013, g32p_row04_traceSegment_067_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1134 27 27, g32p_row04_traceSegment_067_1134_0027, g32p_row04_traceSegment_067_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1080 54 54, g32p_row04_traceSegment_067_1080_0054, g32p_row04_traceSegment_067_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1188 13 14, g32p_row04_traceSegment_067_1188_0013, g32p_row04_traceSegment_067_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1215 13 14, g32p_row04_traceSegment_067_1215_0013, g32p_row04_traceSegment_067_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1188 27 27, g32p_row04_traceSegment_067_1188_0027, g32p_row04_traceSegment_067_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1242 13 14, g32p_row04_traceSegment_067_1242_0013, g32p_row04_traceSegment_067_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1269 13 14, g32p_row04_traceSegment_067_1269_0013, g32p_row04_traceSegment_067_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1242 27 27, g32p_row04_traceSegment_067_1242_0027, g32p_row04_traceSegment_067_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1188 54 54, g32p_row04_traceSegment_067_1188_0054, g32p_row04_traceSegment_067_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1080 108 108, g32p_row04_traceSegment_067_1080_0108, g32p_row04_traceSegment_067_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_067 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 864 216 216, g32p_row04_traceSegment_067_0864_0216, g32p_row04_traceSegment_067_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1296 13 14, g32p_row04_traceSegment_067_1296_0013, g32p_row04_traceSegment_067_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1323 13 14, g32p_row04_traceSegment_067_1323_0013, g32p_row04_traceSegment_067_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1296 27 27, g32p_row04_traceSegment_067_1296_0027, g32p_row04_traceSegment_067_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1350 13 14, g32p_row04_traceSegment_067_1350_0013, g32p_row04_traceSegment_067_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1377 13 14, g32p_row04_traceSegment_067_1377_0013, g32p_row04_traceSegment_067_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1350 27 27, g32p_row04_traceSegment_067_1350_0027, g32p_row04_traceSegment_067_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1296 54 54, g32p_row04_traceSegment_067_1296_0054, g32p_row04_traceSegment_067_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1404 13 14, g32p_row04_traceSegment_067_1404_0013, g32p_row04_traceSegment_067_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1431 13 14, g32p_row04_traceSegment_067_1431_0013, g32p_row04_traceSegment_067_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1404 27 27, g32p_row04_traceSegment_067_1404_0027, g32p_row04_traceSegment_067_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1458 13 14, g32p_row04_traceSegment_067_1458_0013, g32p_row04_traceSegment_067_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1498 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1485 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1485 13 14, g32p_row04_traceSegment_067_1485_0013, g32p_row04_traceSegment_067_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1458 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1458 27 27, g32p_row04_traceSegment_067_1458_0027, g32p_row04_traceSegment_067_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 1404 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1404 54 54, g32p_row04_traceSegment_067_1404_0054, g32p_row04_traceSegment_067_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 1296 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1296 108 108, g32p_row04_traceSegment_067_1296_0108, g32p_row04_traceSegment_067_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1512 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1512 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1512 13 14, g32p_row04_traceSegment_067_1512_0013, g32p_row04_traceSegment_067_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1539 13 14, g32p_row04_traceSegment_067_1539_0013, g32p_row04_traceSegment_067_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1512 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1512 27 27, g32p_row04_traceSegment_067_1512_0027, g32p_row04_traceSegment_067_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1579 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1566 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1566 13 14, g32p_row04_traceSegment_067_1566_0013, g32p_row04_traceSegment_067_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1606 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1593 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1593 13 14, g32p_row04_traceSegment_067_1593_0013, g32p_row04_traceSegment_067_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1566 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1566 27 27, g32p_row04_traceSegment_067_1566_0027, g32p_row04_traceSegment_067_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 1512 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1512 54 54, g32p_row04_traceSegment_067_1512_0054, g32p_row04_traceSegment_067_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1620 13 14, g32p_row04_traceSegment_067_1620_0013, g32p_row04_traceSegment_067_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1647 13 14, g32p_row04_traceSegment_067_1647_0013, g32p_row04_traceSegment_067_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1620 27 27, g32p_row04_traceSegment_067_1620_0027, g32p_row04_traceSegment_067_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1674 13 14, g32p_row04_traceSegment_067_1674_0013, g32p_row04_traceSegment_067_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_067 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_067 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_067_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_067 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1701 13 14, g32p_row04_traceSegment_067_1701_0013, g32p_row04_traceSegment_067_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_067 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1674 27 27, g32p_row04_traceSegment_067_1674_0027, g32p_row04_traceSegment_067_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_067 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1620 54 54, g32p_row04_traceSegment_067_1620_0054, g32p_row04_traceSegment_067_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_067 1512 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1512 108 108, g32p_row04_traceSegment_067_1512_0108, g32p_row04_traceSegment_067_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_067_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_067 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 1296 216 216, g32p_row04_traceSegment_067_1296_0216, g32p_row04_traceSegment_067_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_067 864 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 864 432 432, g32p_row04_traceSegment_067_0864_0432, g32p_row04_traceSegment_067_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_067_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_067 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_067 0 864 864, g32p_row04_traceSegment_067_0000_0864, g32p_row04_traceSegment_067_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_067 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 67 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_067_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_069 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 69 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_069_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 0 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 0 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 0 13 14, g32p_row04_traceSegment_069_0000_0013, g32p_row04_traceSegment_069_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 27 13 14, g32p_row04_traceSegment_069_0027_0013, g32p_row04_traceSegment_069_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 0 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 0 27 27, g32p_row04_traceSegment_069_0000_0027, g32p_row04_traceSegment_069_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 54 13 14, g32p_row04_traceSegment_069_0054_0013, g32p_row04_traceSegment_069_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 81 13 14, g32p_row04_traceSegment_069_0081_0013, g32p_row04_traceSegment_069_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 54 27 27, g32p_row04_traceSegment_069_0054_0027, g32p_row04_traceSegment_069_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 0 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 0 54 54, g32p_row04_traceSegment_069_0000_0054, g32p_row04_traceSegment_069_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 108 13 14, g32p_row04_traceSegment_069_0108_0013, g32p_row04_traceSegment_069_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 148 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 135 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 135 13 14, g32p_row04_traceSegment_069_0135_0013, g32p_row04_traceSegment_069_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 108 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 108 27 27, g32p_row04_traceSegment_069_0108_0027, g32p_row04_traceSegment_069_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 162 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 175 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 162 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 162 13 14, g32p_row04_traceSegment_069_0162_0013, g32p_row04_traceSegment_069_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 189 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 202 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 189 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 189 13 14, g32p_row04_traceSegment_069_0189_0013, g32p_row04_traceSegment_069_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 162 54 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 162 27 27, g32p_row04_traceSegment_069_0162_0027, g32p_row04_traceSegment_069_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 108 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 108 54 54, g32p_row04_traceSegment_069_0108_0054, g32p_row04_traceSegment_069_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 0 216 = [9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 0 108 108, g32p_row04_traceSegment_069_0000_0108, g32p_row04_traceSegment_069_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 216 13 14, g32p_row04_traceSegment_069_0216_0013, g32p_row04_traceSegment_069_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 243 13 14, g32p_row04_traceSegment_069_0243_0013, g32p_row04_traceSegment_069_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 216 27 27, g32p_row04_traceSegment_069_0216_0027, g32p_row04_traceSegment_069_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 270 13 14, g32p_row04_traceSegment_069_0270_0013, g32p_row04_traceSegment_069_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 297 13 14, g32p_row04_traceSegment_069_0297_0013, g32p_row04_traceSegment_069_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 270 27 27, g32p_row04_traceSegment_069_0270_0027, g32p_row04_traceSegment_069_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 216 54 54, g32p_row04_traceSegment_069_0216_0054, g32p_row04_traceSegment_069_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 324 13 14, g32p_row04_traceSegment_069_0324_0013, g32p_row04_traceSegment_069_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 351 13 14, g32p_row04_traceSegment_069_0351_0013, g32p_row04_traceSegment_069_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 324 27 27, g32p_row04_traceSegment_069_0324_0027, g32p_row04_traceSegment_069_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 378 13 14, g32p_row04_traceSegment_069_0378_0013, g32p_row04_traceSegment_069_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 405 13 14, g32p_row04_traceSegment_069_0405_0013, g32p_row04_traceSegment_069_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 378 27 27, g32p_row04_traceSegment_069_0378_0027, g32p_row04_traceSegment_069_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 324 54 54, g32p_row04_traceSegment_069_0324_0054, g32p_row04_traceSegment_069_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 216 108 108, g32p_row04_traceSegment_069_0216_0108, g32p_row04_traceSegment_069_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_069 0 432 = [9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 0 216 216, g32p_row04_traceSegment_069_0000_0216, g32p_row04_traceSegment_069_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 432 13 14, g32p_row04_traceSegment_069_0432_0013, g32p_row04_traceSegment_069_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 459 13 14, g32p_row04_traceSegment_069_0459_0013, g32p_row04_traceSegment_069_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 432 27 27, g32p_row04_traceSegment_069_0432_0027, g32p_row04_traceSegment_069_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 486 13 14, g32p_row04_traceSegment_069_0486_0013, g32p_row04_traceSegment_069_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 513 13 14, g32p_row04_traceSegment_069_0513_0013, g32p_row04_traceSegment_069_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 486 27 27, g32p_row04_traceSegment_069_0486_0027, g32p_row04_traceSegment_069_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 432 54 54, g32p_row04_traceSegment_069_0432_0054, g32p_row04_traceSegment_069_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 540 13 14, g32p_row04_traceSegment_069_0540_0013, g32p_row04_traceSegment_069_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 567 13 14, g32p_row04_traceSegment_069_0567_0013, g32p_row04_traceSegment_069_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 540 27 27, g32p_row04_traceSegment_069_0540_0027, g32p_row04_traceSegment_069_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 594 13 14, g32p_row04_traceSegment_069_0594_0013, g32p_row04_traceSegment_069_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 621 13 14, g32p_row04_traceSegment_069_0621_0013, g32p_row04_traceSegment_069_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 594 27 27, g32p_row04_traceSegment_069_0594_0027, g32p_row04_traceSegment_069_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 540 54 54, g32p_row04_traceSegment_069_0540_0054, g32p_row04_traceSegment_069_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 432 108 108, g32p_row04_traceSegment_069_0432_0108, g32p_row04_traceSegment_069_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 648 13 14, g32p_row04_traceSegment_069_0648_0013, g32p_row04_traceSegment_069_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 675 13 14, g32p_row04_traceSegment_069_0675_0013, g32p_row04_traceSegment_069_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 648 27 27, g32p_row04_traceSegment_069_0648_0027, g32p_row04_traceSegment_069_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 702 13 14, g32p_row04_traceSegment_069_0702_0013, g32p_row04_traceSegment_069_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 729 13 14, g32p_row04_traceSegment_069_0729_0013, g32p_row04_traceSegment_069_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 702 27 27, g32p_row04_traceSegment_069_0702_0027, g32p_row04_traceSegment_069_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 648 54 54, g32p_row04_traceSegment_069_0648_0054, g32p_row04_traceSegment_069_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 756 13 14, g32p_row04_traceSegment_069_0756_0013, g32p_row04_traceSegment_069_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 783 13 14, g32p_row04_traceSegment_069_0783_0013, g32p_row04_traceSegment_069_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 756 27 27, g32p_row04_traceSegment_069_0756_0027, g32p_row04_traceSegment_069_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 823 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 810 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 810 13 14, g32p_row04_traceSegment_069_0810_0013, g32p_row04_traceSegment_069_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 850 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 837 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 837 13 14, g32p_row04_traceSegment_069_0837_0013, g32p_row04_traceSegment_069_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 810 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 810 27 27, g32p_row04_traceSegment_069_0810_0027, g32p_row04_traceSegment_069_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 756 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 756 54 54, g32p_row04_traceSegment_069_0756_0054, g32p_row04_traceSegment_069_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 648 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 648 108 108, g32p_row04_traceSegment_069_0648_0108, g32p_row04_traceSegment_069_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_069 432 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 432 216 216, g32p_row04_traceSegment_069_0432_0216, g32p_row04_traceSegment_069_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_069 0 864 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 0 432 432, g32p_row04_traceSegment_069_0000_0432, g32p_row04_traceSegment_069_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 877 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 864 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 864 13 14, g32p_row04_traceSegment_069_0864_0013, g32p_row04_traceSegment_069_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 891 13 14, g32p_row04_traceSegment_069_0891_0013, g32p_row04_traceSegment_069_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 864 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 864 27 27, g32p_row04_traceSegment_069_0864_0027, g32p_row04_traceSegment_069_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 918 13 14, g32p_row04_traceSegment_069_0918_0013, g32p_row04_traceSegment_069_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 945 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 958 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 945 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 945 13 14, g32p_row04_traceSegment_069_0945_0013, g32p_row04_traceSegment_069_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 918 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 918 27 27, g32p_row04_traceSegment_069_0918_0027, g32p_row04_traceSegment_069_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 864 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 864 54 54, g32p_row04_traceSegment_069_0864_0054, g32p_row04_traceSegment_069_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 972 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 972 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 972 13 14, g32p_row04_traceSegment_069_0972_0013, g32p_row04_traceSegment_069_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1012 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 999 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 999 13 14, g32p_row04_traceSegment_069_0999_0013, g32p_row04_traceSegment_069_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 972 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 972 27 27, g32p_row04_traceSegment_069_0972_0027, g32p_row04_traceSegment_069_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1026 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1026 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1026 13 14, g32p_row04_traceSegment_069_1026_0013, g32p_row04_traceSegment_069_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1053 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1066 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1053 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1053 13 14, g32p_row04_traceSegment_069_1053_0013, g32p_row04_traceSegment_069_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1026 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1026 27 27, g32p_row04_traceSegment_069_1026_0027, g32p_row04_traceSegment_069_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 972 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 972 54 54, g32p_row04_traceSegment_069_0972_0054, g32p_row04_traceSegment_069_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 864 216 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 864 108 108, g32p_row04_traceSegment_069_0864_0108, g32p_row04_traceSegment_069_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1080 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1080 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1080 13 14, g32p_row04_traceSegment_069_1080_0013, g32p_row04_traceSegment_069_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1120 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1107 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1107 13 14, g32p_row04_traceSegment_069_1107_0013, g32p_row04_traceSegment_069_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1080 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1080 27 27, g32p_row04_traceSegment_069_1080_0027, g32p_row04_traceSegment_069_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1134 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1147 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1134 27 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1134 13 14, g32p_row04_traceSegment_069_1134_0013, g32p_row04_traceSegment_069_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1161 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1161 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1161 13 14, g32p_row04_traceSegment_069_1161_0013, g32p_row04_traceSegment_069_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1134 54 = [9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1134 27 27, g32p_row04_traceSegment_069_1134_0027, g32p_row04_traceSegment_069_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 1080 108 = [11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1080 54 54, g32p_row04_traceSegment_069_1080_0054, g32p_row04_traceSegment_069_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1188 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1188 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1188 13 14, g32p_row04_traceSegment_069_1188_0013, g32p_row04_traceSegment_069_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1215 13 14, g32p_row04_traceSegment_069_1215_0013, g32p_row04_traceSegment_069_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1188 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1188 27 27, g32p_row04_traceSegment_069_1188_0027, g32p_row04_traceSegment_069_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1242 13 14, g32p_row04_traceSegment_069_1242_0013, g32p_row04_traceSegment_069_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1269 13 14, g32p_row04_traceSegment_069_1269_0013, g32p_row04_traceSegment_069_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1242 27 27, g32p_row04_traceSegment_069_1242_0027, g32p_row04_traceSegment_069_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 1188 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1188 54 54, g32p_row04_traceSegment_069_1188_0054, g32p_row04_traceSegment_069_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 1080 216 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1080 108 108, g32p_row04_traceSegment_069_1080_0108, g32p_row04_traceSegment_069_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_069 864 432 = [24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 864 216 216, g32p_row04_traceSegment_069_0864_0216, g32p_row04_traceSegment_069_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1296 13 14, g32p_row04_traceSegment_069_1296_0013, g32p_row04_traceSegment_069_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1323 13 14, g32p_row04_traceSegment_069_1323_0013, g32p_row04_traceSegment_069_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1296 27 27, g32p_row04_traceSegment_069_1296_0027, g32p_row04_traceSegment_069_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1350 13 14, g32p_row04_traceSegment_069_1350_0013, g32p_row04_traceSegment_069_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1377 13 14, g32p_row04_traceSegment_069_1377_0013, g32p_row04_traceSegment_069_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1350 27 27, g32p_row04_traceSegment_069_1350_0027, g32p_row04_traceSegment_069_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1296 54 54, g32p_row04_traceSegment_069_1296_0054, g32p_row04_traceSegment_069_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1404 13 14, g32p_row04_traceSegment_069_1404_0013, g32p_row04_traceSegment_069_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1431 13 14, g32p_row04_traceSegment_069_1431_0013, g32p_row04_traceSegment_069_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1404 27 27, g32p_row04_traceSegment_069_1404_0027, g32p_row04_traceSegment_069_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1458 13 14, g32p_row04_traceSegment_069_1458_0013, g32p_row04_traceSegment_069_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1485 13 14, g32p_row04_traceSegment_069_1485_0013, g32p_row04_traceSegment_069_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1458 27 27, g32p_row04_traceSegment_069_1458_0027, g32p_row04_traceSegment_069_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1404 54 54, g32p_row04_traceSegment_069_1404_0054, g32p_row04_traceSegment_069_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1296 108 108, g32p_row04_traceSegment_069_1296_0108, g32p_row04_traceSegment_069_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1512 13 14, g32p_row04_traceSegment_069_1512_0013, g32p_row04_traceSegment_069_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1539 13 14, g32p_row04_traceSegment_069_1539_0013, g32p_row04_traceSegment_069_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1512 27 27, g32p_row04_traceSegment_069_1512_0027, g32p_row04_traceSegment_069_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1566 13 14, g32p_row04_traceSegment_069_1566_0013, g32p_row04_traceSegment_069_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1593 13 14, g32p_row04_traceSegment_069_1593_0013, g32p_row04_traceSegment_069_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1566 27 27, g32p_row04_traceSegment_069_1566_0027, g32p_row04_traceSegment_069_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1512 54 54, g32p_row04_traceSegment_069_1512_0054, g32p_row04_traceSegment_069_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1620 13 14, g32p_row04_traceSegment_069_1620_0013, g32p_row04_traceSegment_069_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1647 13 14, g32p_row04_traceSegment_069_1647_0013, g32p_row04_traceSegment_069_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1620 27 27, g32p_row04_traceSegment_069_1620_0027, g32p_row04_traceSegment_069_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1674 13 14, g32p_row04_traceSegment_069_1674_0013, g32p_row04_traceSegment_069_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_069 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_069 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_069_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_069 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1701 13 14, g32p_row04_traceSegment_069_1701_0013, g32p_row04_traceSegment_069_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_069 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1674 27 27, g32p_row04_traceSegment_069_1674_0027, g32p_row04_traceSegment_069_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_069 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1620 54 54, g32p_row04_traceSegment_069_1620_0054, g32p_row04_traceSegment_069_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_069 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1512 108 108, g32p_row04_traceSegment_069_1512_0108, g32p_row04_traceSegment_069_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_069_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_069 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 1296 216 216, g32p_row04_traceSegment_069_1296_0216, g32p_row04_traceSegment_069_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_069 864 864 = [24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 864 432 432, g32p_row04_traceSegment_069_0864_0432, g32p_row04_traceSegment_069_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_069_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_069 0 1728 = [36] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_069 0 864 864, g32p_row04_traceSegment_069_0000_0864, g32p_row04_traceSegment_069_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_069 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 69 = [36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_069_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_059 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 59) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 59) (g32p_literalTraceValue 3 59)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_059]
  decide +kernel

theorem g32p_row04_tracePolynomial_061 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 61) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 61) (g32p_literalTraceValue 3 61)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_061]
  decide +kernel

theorem g32p_row04_tracePolynomial_063 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 63) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 63) (g32p_literalTraceValue 3 63)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_063]
  decide +kernel

theorem g32p_row04_tracePolynomial_064 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 64) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 64) (g32p_literalTraceValue 3 64)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_064]
  decide +kernel

theorem g32p_row04_tracePolynomial_065 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 65) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 65) (g32p_literalTraceValue 3 65)
      [1, 1, 1] [3456] = true := by
  rw [g32p_row04_traceCoefficients_065]
  decide +kernel

theorem g32p_row04_tracePolynomial_066 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 66) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 66) (g32p_literalTraceValue 3 66)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_066]
  decide +kernel

theorem g32p_row04_tracePolynomial_067 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 67) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 67) (g32p_literalTraceValue 3 67)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_067]
  decide +kernel

theorem g32p_row04_tracePolynomial_069 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 69) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 69) (g32p_literalTraceValue 3 69)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_069]
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

private def g32p_row04_traceSegment_071 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 71 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_071_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 0 13 14, g32p_row04_traceSegment_071_0000_0013, g32p_row04_traceSegment_071_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 27 13 14, g32p_row04_traceSegment_071_0027_0013, g32p_row04_traceSegment_071_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 0 27 27, g32p_row04_traceSegment_071_0000_0027, g32p_row04_traceSegment_071_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 54 13 14, g32p_row04_traceSegment_071_0054_0013, g32p_row04_traceSegment_071_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 81 13 14, g32p_row04_traceSegment_071_0081_0013, g32p_row04_traceSegment_071_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 54 27 27, g32p_row04_traceSegment_071_0054_0027, g32p_row04_traceSegment_071_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 0 54 54, g32p_row04_traceSegment_071_0000_0054, g32p_row04_traceSegment_071_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 108 13 14, g32p_row04_traceSegment_071_0108_0013, g32p_row04_traceSegment_071_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 135 13 14, g32p_row04_traceSegment_071_0135_0013, g32p_row04_traceSegment_071_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 108 27 27, g32p_row04_traceSegment_071_0108_0027, g32p_row04_traceSegment_071_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 162 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 175 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 162 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 162 13 14, g32p_row04_traceSegment_071_0162_0013, g32p_row04_traceSegment_071_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 202 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 189 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 189 13 14, g32p_row04_traceSegment_071_0189_0013, g32p_row04_traceSegment_071_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 162 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 162 27 27, g32p_row04_traceSegment_071_0162_0027, g32p_row04_traceSegment_071_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 108 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 108 54 54, g32p_row04_traceSegment_071_0108_0054, g32p_row04_traceSegment_071_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 0 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 0 108 108, g32p_row04_traceSegment_071_0000_0108, g32p_row04_traceSegment_071_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 216 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 229 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 216 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 216 13 14, g32p_row04_traceSegment_071_0216_0013, g32p_row04_traceSegment_071_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 243 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 243 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 243 13 14, g32p_row04_traceSegment_071_0243_0013, g32p_row04_traceSegment_071_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 216 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 216 27 27, g32p_row04_traceSegment_071_0216_0027, g32p_row04_traceSegment_071_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 270 13 14, g32p_row04_traceSegment_071_0270_0013, g32p_row04_traceSegment_071_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 297 13 14, g32p_row04_traceSegment_071_0297_0013, g32p_row04_traceSegment_071_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 270 27 27, g32p_row04_traceSegment_071_0270_0027, g32p_row04_traceSegment_071_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 216 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 216 54 54, g32p_row04_traceSegment_071_0216_0054, g32p_row04_traceSegment_071_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 324 13 14, g32p_row04_traceSegment_071_0324_0013, g32p_row04_traceSegment_071_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 351 13 14, g32p_row04_traceSegment_071_0351_0013, g32p_row04_traceSegment_071_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 324 27 27, g32p_row04_traceSegment_071_0324_0027, g32p_row04_traceSegment_071_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 378 13 14, g32p_row04_traceSegment_071_0378_0013, g32p_row04_traceSegment_071_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 405 13 14, g32p_row04_traceSegment_071_0405_0013, g32p_row04_traceSegment_071_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 378 27 27, g32p_row04_traceSegment_071_0378_0027, g32p_row04_traceSegment_071_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 324 54 54, g32p_row04_traceSegment_071_0324_0054, g32p_row04_traceSegment_071_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 216 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 216 108 108, g32p_row04_traceSegment_071_0216_0108, g32p_row04_traceSegment_071_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_071 0 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 0 216 216, g32p_row04_traceSegment_071_0000_0216, g32p_row04_traceSegment_071_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 432 13 14, g32p_row04_traceSegment_071_0432_0013, g32p_row04_traceSegment_071_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 459 13 14, g32p_row04_traceSegment_071_0459_0013, g32p_row04_traceSegment_071_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 432 27 27, g32p_row04_traceSegment_071_0432_0027, g32p_row04_traceSegment_071_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 486 13 14, g32p_row04_traceSegment_071_0486_0013, g32p_row04_traceSegment_071_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 513 13 14, g32p_row04_traceSegment_071_0513_0013, g32p_row04_traceSegment_071_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 486 27 27, g32p_row04_traceSegment_071_0486_0027, g32p_row04_traceSegment_071_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 432 54 54, g32p_row04_traceSegment_071_0432_0054, g32p_row04_traceSegment_071_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 540 13 14, g32p_row04_traceSegment_071_0540_0013, g32p_row04_traceSegment_071_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 567 13 14, g32p_row04_traceSegment_071_0567_0013, g32p_row04_traceSegment_071_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 540 27 27, g32p_row04_traceSegment_071_0540_0027, g32p_row04_traceSegment_071_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 594 13 14, g32p_row04_traceSegment_071_0594_0013, g32p_row04_traceSegment_071_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 621 13 14, g32p_row04_traceSegment_071_0621_0013, g32p_row04_traceSegment_071_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 594 27 27, g32p_row04_traceSegment_071_0594_0027, g32p_row04_traceSegment_071_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 540 54 54, g32p_row04_traceSegment_071_0540_0054, g32p_row04_traceSegment_071_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 432 108 108, g32p_row04_traceSegment_071_0432_0108, g32p_row04_traceSegment_071_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 648 13 14, g32p_row04_traceSegment_071_0648_0013, g32p_row04_traceSegment_071_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 675 13 14, g32p_row04_traceSegment_071_0675_0013, g32p_row04_traceSegment_071_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 648 27 27, g32p_row04_traceSegment_071_0648_0027, g32p_row04_traceSegment_071_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 702 13 14, g32p_row04_traceSegment_071_0702_0013, g32p_row04_traceSegment_071_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 729 13 14, g32p_row04_traceSegment_071_0729_0013, g32p_row04_traceSegment_071_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 702 27 27, g32p_row04_traceSegment_071_0702_0027, g32p_row04_traceSegment_071_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 648 54 54, g32p_row04_traceSegment_071_0648_0054, g32p_row04_traceSegment_071_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 756 13 14, g32p_row04_traceSegment_071_0756_0013, g32p_row04_traceSegment_071_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 783 13 14, g32p_row04_traceSegment_071_0783_0013, g32p_row04_traceSegment_071_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 756 27 27, g32p_row04_traceSegment_071_0756_0027, g32p_row04_traceSegment_071_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 810 13 14, g32p_row04_traceSegment_071_0810_0013, g32p_row04_traceSegment_071_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 837 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 850 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 837 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 837 13 14, g32p_row04_traceSegment_071_0837_0013, g32p_row04_traceSegment_071_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 810 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 810 27 27, g32p_row04_traceSegment_071_0810_0027, g32p_row04_traceSegment_071_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 756 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 756 54 54, g32p_row04_traceSegment_071_0756_0054, g32p_row04_traceSegment_071_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 648 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 648 108 108, g32p_row04_traceSegment_071_0648_0108, g32p_row04_traceSegment_071_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_071 432 432 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 432 216 216, g32p_row04_traceSegment_071_0432_0216, g32p_row04_traceSegment_071_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_071 0 864 = [0, 4, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 0 432 432, g32p_row04_traceSegment_071_0000_0432, g32p_row04_traceSegment_071_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 877 14 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 864 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 864 13 14, g32p_row04_traceSegment_071_0864_0013, g32p_row04_traceSegment_071_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 891 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 904 14 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 891 27 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 891 13 14, g32p_row04_traceSegment_071_0891_0013, g32p_row04_traceSegment_071_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 864 54 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 864 27 27, g32p_row04_traceSegment_071_0864_0027, g32p_row04_traceSegment_071_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 918 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 931 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 918 27 = [0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 918 13 14, g32p_row04_traceSegment_071_0918_0013, g32p_row04_traceSegment_071_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 945 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 958 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 945 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 945 13 14, g32p_row04_traceSegment_071_0945_0013, g32p_row04_traceSegment_071_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 918 54 = [0, 4, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 918 27 27, g32p_row04_traceSegment_071_0918_0027, g32p_row04_traceSegment_071_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 864 108 = [0, 6, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 864 54 54, g32p_row04_traceSegment_071_0864_0054, g32p_row04_traceSegment_071_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 972 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 985 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 972 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 972 13 14, g32p_row04_traceSegment_071_0972_0013, g32p_row04_traceSegment_071_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 999 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1012 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 999 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 999 13 14, g32p_row04_traceSegment_071_0999_0013, g32p_row04_traceSegment_071_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 972 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 972 27 27, g32p_row04_traceSegment_071_0972_0027, g32p_row04_traceSegment_071_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1026 13 14, g32p_row04_traceSegment_071_1026_0013, g32p_row04_traceSegment_071_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1053 13 14, g32p_row04_traceSegment_071_1053_0013, g32p_row04_traceSegment_071_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1026 27 27, g32p_row04_traceSegment_071_1026_0027, g32p_row04_traceSegment_071_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 972 108 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 972 54 54, g32p_row04_traceSegment_071_0972_0054, g32p_row04_traceSegment_071_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 864 216 = [0, 11, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 864 108 108, g32p_row04_traceSegment_071_0864_0108, g32p_row04_traceSegment_071_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1080 13 14, g32p_row04_traceSegment_071_1080_0013, g32p_row04_traceSegment_071_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1107 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1107 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1107 13 14, g32p_row04_traceSegment_071_1107_0013, g32p_row04_traceSegment_071_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1080 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1080 27 27, g32p_row04_traceSegment_071_1080_0027, g32p_row04_traceSegment_071_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1134 13 14, g32p_row04_traceSegment_071_1134_0013, g32p_row04_traceSegment_071_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1174 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1161 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1161 13 14, g32p_row04_traceSegment_071_1161_0013, g32p_row04_traceSegment_071_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1134 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1134 27 27, g32p_row04_traceSegment_071_1134_0027, g32p_row04_traceSegment_071_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 1080 108 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1080 54 54, g32p_row04_traceSegment_071_1080_0054, g32p_row04_traceSegment_071_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1188 13 14, g32p_row04_traceSegment_071_1188_0013, g32p_row04_traceSegment_071_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1215 13 14, g32p_row04_traceSegment_071_1215_0013, g32p_row04_traceSegment_071_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1188 27 27, g32p_row04_traceSegment_071_1188_0027, g32p_row04_traceSegment_071_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1242 13 14, g32p_row04_traceSegment_071_1242_0013, g32p_row04_traceSegment_071_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1269 13 14, g32p_row04_traceSegment_071_1269_0013, g32p_row04_traceSegment_071_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1242 27 27, g32p_row04_traceSegment_071_1242_0027, g32p_row04_traceSegment_071_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1188 54 54, g32p_row04_traceSegment_071_1188_0054, g32p_row04_traceSegment_071_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 1080 216 = [0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1080 108 108, g32p_row04_traceSegment_071_1080_0108, g32p_row04_traceSegment_071_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_071 864 432 = [0, 12, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 864 216 216, g32p_row04_traceSegment_071_0864_0216, g32p_row04_traceSegment_071_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1296 13 14, g32p_row04_traceSegment_071_1296_0013, g32p_row04_traceSegment_071_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1323 13 14, g32p_row04_traceSegment_071_1323_0013, g32p_row04_traceSegment_071_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1296 27 27, g32p_row04_traceSegment_071_1296_0027, g32p_row04_traceSegment_071_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1350 13 14, g32p_row04_traceSegment_071_1350_0013, g32p_row04_traceSegment_071_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1377 13 14, g32p_row04_traceSegment_071_1377_0013, g32p_row04_traceSegment_071_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1350 27 27, g32p_row04_traceSegment_071_1350_0027, g32p_row04_traceSegment_071_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1296 54 54, g32p_row04_traceSegment_071_1296_0054, g32p_row04_traceSegment_071_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1404 13 14, g32p_row04_traceSegment_071_1404_0013, g32p_row04_traceSegment_071_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1431 13 14, g32p_row04_traceSegment_071_1431_0013, g32p_row04_traceSegment_071_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1404 27 27, g32p_row04_traceSegment_071_1404_0027, g32p_row04_traceSegment_071_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1458 13 14, g32p_row04_traceSegment_071_1458_0013, g32p_row04_traceSegment_071_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1485 13 14, g32p_row04_traceSegment_071_1485_0013, g32p_row04_traceSegment_071_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1458 27 27, g32p_row04_traceSegment_071_1458_0027, g32p_row04_traceSegment_071_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1404 54 54, g32p_row04_traceSegment_071_1404_0054, g32p_row04_traceSegment_071_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1296 108 108, g32p_row04_traceSegment_071_1296_0108, g32p_row04_traceSegment_071_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1512 13 14, g32p_row04_traceSegment_071_1512_0013, g32p_row04_traceSegment_071_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1539 13 14, g32p_row04_traceSegment_071_1539_0013, g32p_row04_traceSegment_071_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1512 27 27, g32p_row04_traceSegment_071_1512_0027, g32p_row04_traceSegment_071_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1566 13 14, g32p_row04_traceSegment_071_1566_0013, g32p_row04_traceSegment_071_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1593 13 14, g32p_row04_traceSegment_071_1593_0013, g32p_row04_traceSegment_071_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1566 27 27, g32p_row04_traceSegment_071_1566_0027, g32p_row04_traceSegment_071_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1512 54 54, g32p_row04_traceSegment_071_1512_0054, g32p_row04_traceSegment_071_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1620 13 14, g32p_row04_traceSegment_071_1620_0013, g32p_row04_traceSegment_071_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1647 13 14, g32p_row04_traceSegment_071_1647_0013, g32p_row04_traceSegment_071_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1620 27 27, g32p_row04_traceSegment_071_1620_0027, g32p_row04_traceSegment_071_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1674 13 14, g32p_row04_traceSegment_071_1674_0013, g32p_row04_traceSegment_071_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_071 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_071 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_071_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_071 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1701 13 14, g32p_row04_traceSegment_071_1701_0013, g32p_row04_traceSegment_071_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_071 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1674 27 27, g32p_row04_traceSegment_071_1674_0027, g32p_row04_traceSegment_071_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_071 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1620 54 54, g32p_row04_traceSegment_071_1620_0054, g32p_row04_traceSegment_071_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_071 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1512 108 108, g32p_row04_traceSegment_071_1512_0108, g32p_row04_traceSegment_071_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_071_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_071 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 1296 216 216, g32p_row04_traceSegment_071_1296_0216, g32p_row04_traceSegment_071_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_071 864 864 = [0, 12, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 864 432 432, g32p_row04_traceSegment_071_0864_0432, g32p_row04_traceSegment_071_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_071_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_071 0 1728 = [0, 16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_071 0 864 864, g32p_row04_traceSegment_071_0000_0864, g32p_row04_traceSegment_071_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_071 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 71 = [0, 16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_071_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_072 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 72 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_072_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 0 13 14, g32p_row04_traceSegment_072_0000_0013, g32p_row04_traceSegment_072_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 27 13 14, g32p_row04_traceSegment_072_0027_0013, g32p_row04_traceSegment_072_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 0 27 27, g32p_row04_traceSegment_072_0000_0027, g32p_row04_traceSegment_072_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 54 13 14, g32p_row04_traceSegment_072_0054_0013, g32p_row04_traceSegment_072_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 81 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 94 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 81 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 81 13 14, g32p_row04_traceSegment_072_0081_0013, g32p_row04_traceSegment_072_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 54 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 54 27 27, g32p_row04_traceSegment_072_0054_0027, g32p_row04_traceSegment_072_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 0 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 0 54 54, g32p_row04_traceSegment_072_0000_0054, g32p_row04_traceSegment_072_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 108 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 121 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 108 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 108 13 14, g32p_row04_traceSegment_072_0108_0013, g32p_row04_traceSegment_072_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 135 13 14, g32p_row04_traceSegment_072_0135_0013, g32p_row04_traceSegment_072_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 108 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 108 27 27, g32p_row04_traceSegment_072_0108_0027, g32p_row04_traceSegment_072_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 162 13 14, g32p_row04_traceSegment_072_0162_0013, g32p_row04_traceSegment_072_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 189 13 14, g32p_row04_traceSegment_072_0189_0013, g32p_row04_traceSegment_072_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 162 27 27, g32p_row04_traceSegment_072_0162_0027, g32p_row04_traceSegment_072_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 108 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 108 54 54, g32p_row04_traceSegment_072_0108_0054, g32p_row04_traceSegment_072_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 0 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 0 108 108, g32p_row04_traceSegment_072_0000_0108, g32p_row04_traceSegment_072_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 216 13 14, g32p_row04_traceSegment_072_0216_0013, g32p_row04_traceSegment_072_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 243 13 14, g32p_row04_traceSegment_072_0243_0013, g32p_row04_traceSegment_072_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 216 27 27, g32p_row04_traceSegment_072_0216_0027, g32p_row04_traceSegment_072_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 270 13 14, g32p_row04_traceSegment_072_0270_0013, g32p_row04_traceSegment_072_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 297 13 14, g32p_row04_traceSegment_072_0297_0013, g32p_row04_traceSegment_072_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 270 27 27, g32p_row04_traceSegment_072_0270_0027, g32p_row04_traceSegment_072_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 216 54 54, g32p_row04_traceSegment_072_0216_0054, g32p_row04_traceSegment_072_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 324 13 14, g32p_row04_traceSegment_072_0324_0013, g32p_row04_traceSegment_072_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 351 13 14, g32p_row04_traceSegment_072_0351_0013, g32p_row04_traceSegment_072_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 324 27 27, g32p_row04_traceSegment_072_0324_0027, g32p_row04_traceSegment_072_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 378 13 14, g32p_row04_traceSegment_072_0378_0013, g32p_row04_traceSegment_072_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 405 13 14, g32p_row04_traceSegment_072_0405_0013, g32p_row04_traceSegment_072_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 378 27 27, g32p_row04_traceSegment_072_0378_0027, g32p_row04_traceSegment_072_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 324 54 54, g32p_row04_traceSegment_072_0324_0054, g32p_row04_traceSegment_072_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 216 108 108, g32p_row04_traceSegment_072_0216_0108, g32p_row04_traceSegment_072_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_072 0 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 0 216 216, g32p_row04_traceSegment_072_0000_0216, g32p_row04_traceSegment_072_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 432 13 14, g32p_row04_traceSegment_072_0432_0013, g32p_row04_traceSegment_072_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 459 13 14, g32p_row04_traceSegment_072_0459_0013, g32p_row04_traceSegment_072_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 432 27 27, g32p_row04_traceSegment_072_0432_0027, g32p_row04_traceSegment_072_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 486 13 14, g32p_row04_traceSegment_072_0486_0013, g32p_row04_traceSegment_072_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 513 13 = [4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 526 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 513 27 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 513 13 14, g32p_row04_traceSegment_072_0513_0013, g32p_row04_traceSegment_072_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 486 54 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 486 27 27, g32p_row04_traceSegment_072_0486_0027, g32p_row04_traceSegment_072_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 432 108 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 432 54 54, g32p_row04_traceSegment_072_0432_0054, g32p_row04_traceSegment_072_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 540 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 553 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 540 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 540 13 14, g32p_row04_traceSegment_072_0540_0013, g32p_row04_traceSegment_072_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 567 13 14, g32p_row04_traceSegment_072_0567_0013, g32p_row04_traceSegment_072_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 540 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 540 27 27, g32p_row04_traceSegment_072_0540_0027, g32p_row04_traceSegment_072_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 607 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 594 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 594 13 14, g32p_row04_traceSegment_072_0594_0013, g32p_row04_traceSegment_072_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 621 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 634 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 621 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 621 13 14, g32p_row04_traceSegment_072_0621_0013, g32p_row04_traceSegment_072_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 594 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 594 27 27, g32p_row04_traceSegment_072_0594_0027, g32p_row04_traceSegment_072_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 540 108 = [3, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 540 54 54, g32p_row04_traceSegment_072_0540_0054, g32p_row04_traceSegment_072_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 432 216 = [10, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 432 108 108, g32p_row04_traceSegment_072_0432_0108, g32p_row04_traceSegment_072_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 648 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 661 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 648 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 648 13 14, g32p_row04_traceSegment_072_0648_0013, g32p_row04_traceSegment_072_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 688 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 675 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 675 13 14, g32p_row04_traceSegment_072_0675_0013, g32p_row04_traceSegment_072_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 648 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 648 27 27, g32p_row04_traceSegment_072_0648_0027, g32p_row04_traceSegment_072_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 702 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 715 14 = [2, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 702 27 = [2, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 702 13 14, g32p_row04_traceSegment_072_0702_0013, g32p_row04_traceSegment_072_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 742 14 = [1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 729 27 = [1, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 729 13 14, g32p_row04_traceSegment_072_0729_0013, g32p_row04_traceSegment_072_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 702 54 = [3, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 702 27 27, g32p_row04_traceSegment_072_0702_0027, g32p_row04_traceSegment_072_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 648 108 = [3, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 648 54 54, g32p_row04_traceSegment_072_0648_0054, g32p_row04_traceSegment_072_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 769 14 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 756 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 756 13 14, g32p_row04_traceSegment_072_0756_0013, g32p_row04_traceSegment_072_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 783 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 796 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 783 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 783 13 14, g32p_row04_traceSegment_072_0783_0013, g32p_row04_traceSegment_072_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 756 54 = [3, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 756 27 27, g32p_row04_traceSegment_072_0756_0027, g32p_row04_traceSegment_072_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 810 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 823 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 810 27 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 810 13 14, g32p_row04_traceSegment_072_0810_0013, g32p_row04_traceSegment_072_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 837 13 14, g32p_row04_traceSegment_072_0837_0013, g32p_row04_traceSegment_072_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 810 54 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 810 27 27, g32p_row04_traceSegment_072_0810_0027, g32p_row04_traceSegment_072_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 756 108 = [4, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 756 54 54, g32p_row04_traceSegment_072_0756_0054, g32p_row04_traceSegment_072_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 648 216 = [7, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 648 108 108, g32p_row04_traceSegment_072_0648_0108, g32p_row04_traceSegment_072_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_072 432 432 = [17, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 432 216 216, g32p_row04_traceSegment_072_0432_0216, g32p_row04_traceSegment_072_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_072 0 864 = [23, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 0 432 432, g32p_row04_traceSegment_072_0000_0432, g32p_row04_traceSegment_072_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 864 13 14, g32p_row04_traceSegment_072_0864_0013, g32p_row04_traceSegment_072_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 891 13 14, g32p_row04_traceSegment_072_0891_0013, g32p_row04_traceSegment_072_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 864 27 27, g32p_row04_traceSegment_072_0864_0027, g32p_row04_traceSegment_072_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 918 13 14, g32p_row04_traceSegment_072_0918_0013, g32p_row04_traceSegment_072_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 945 13 14, g32p_row04_traceSegment_072_0945_0013, g32p_row04_traceSegment_072_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 918 27 27, g32p_row04_traceSegment_072_0918_0027, g32p_row04_traceSegment_072_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 864 54 54, g32p_row04_traceSegment_072_0864_0054, g32p_row04_traceSegment_072_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 972 13 14, g32p_row04_traceSegment_072_0972_0013, g32p_row04_traceSegment_072_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 999 13 14, g32p_row04_traceSegment_072_0999_0013, g32p_row04_traceSegment_072_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 972 27 27, g32p_row04_traceSegment_072_0972_0027, g32p_row04_traceSegment_072_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1026 13 14, g32p_row04_traceSegment_072_1026_0013, g32p_row04_traceSegment_072_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1053 13 14, g32p_row04_traceSegment_072_1053_0013, g32p_row04_traceSegment_072_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1026 27 27, g32p_row04_traceSegment_072_1026_0027, g32p_row04_traceSegment_072_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 972 54 54, g32p_row04_traceSegment_072_0972_0054, g32p_row04_traceSegment_072_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 864 108 108, g32p_row04_traceSegment_072_0864_0108, g32p_row04_traceSegment_072_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1080 13 14, g32p_row04_traceSegment_072_1080_0013, g32p_row04_traceSegment_072_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1107 13 14, g32p_row04_traceSegment_072_1107_0013, g32p_row04_traceSegment_072_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1080 27 27, g32p_row04_traceSegment_072_1080_0027, g32p_row04_traceSegment_072_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1134 13 14, g32p_row04_traceSegment_072_1134_0013, g32p_row04_traceSegment_072_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1161 13 14, g32p_row04_traceSegment_072_1161_0013, g32p_row04_traceSegment_072_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1134 27 27, g32p_row04_traceSegment_072_1134_0027, g32p_row04_traceSegment_072_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1080 54 54, g32p_row04_traceSegment_072_1080_0054, g32p_row04_traceSegment_072_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1188 13 14, g32p_row04_traceSegment_072_1188_0013, g32p_row04_traceSegment_072_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1215 13 14, g32p_row04_traceSegment_072_1215_0013, g32p_row04_traceSegment_072_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1188 27 27, g32p_row04_traceSegment_072_1188_0027, g32p_row04_traceSegment_072_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1242 13 14, g32p_row04_traceSegment_072_1242_0013, g32p_row04_traceSegment_072_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1269 13 14, g32p_row04_traceSegment_072_1269_0013, g32p_row04_traceSegment_072_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1242 27 27, g32p_row04_traceSegment_072_1242_0027, g32p_row04_traceSegment_072_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1188 54 54, g32p_row04_traceSegment_072_1188_0054, g32p_row04_traceSegment_072_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1080 108 108, g32p_row04_traceSegment_072_1080_0108, g32p_row04_traceSegment_072_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_072 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 864 216 216, g32p_row04_traceSegment_072_0864_0216, g32p_row04_traceSegment_072_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1296 13 14, g32p_row04_traceSegment_072_1296_0013, g32p_row04_traceSegment_072_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1323 13 14, g32p_row04_traceSegment_072_1323_0013, g32p_row04_traceSegment_072_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1296 27 27, g32p_row04_traceSegment_072_1296_0027, g32p_row04_traceSegment_072_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1350 13 14, g32p_row04_traceSegment_072_1350_0013, g32p_row04_traceSegment_072_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1377 13 14, g32p_row04_traceSegment_072_1377_0013, g32p_row04_traceSegment_072_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1350 27 27, g32p_row04_traceSegment_072_1350_0027, g32p_row04_traceSegment_072_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1296 54 54, g32p_row04_traceSegment_072_1296_0054, g32p_row04_traceSegment_072_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1404 13 14, g32p_row04_traceSegment_072_1404_0013, g32p_row04_traceSegment_072_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1431 13 14, g32p_row04_traceSegment_072_1431_0013, g32p_row04_traceSegment_072_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1404 27 27, g32p_row04_traceSegment_072_1404_0027, g32p_row04_traceSegment_072_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1458 13 14, g32p_row04_traceSegment_072_1458_0013, g32p_row04_traceSegment_072_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1485 13 14, g32p_row04_traceSegment_072_1485_0013, g32p_row04_traceSegment_072_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1458 27 27, g32p_row04_traceSegment_072_1458_0027, g32p_row04_traceSegment_072_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1404 54 54, g32p_row04_traceSegment_072_1404_0054, g32p_row04_traceSegment_072_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1296 108 108, g32p_row04_traceSegment_072_1296_0108, g32p_row04_traceSegment_072_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1525 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1512 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1512 13 14, g32p_row04_traceSegment_072_1512_0013, g32p_row04_traceSegment_072_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1539 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1552 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1539 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1539 13 14, g32p_row04_traceSegment_072_1539_0013, g32p_row04_traceSegment_072_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1512 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1512 27 27, g32p_row04_traceSegment_072_1512_0027, g32p_row04_traceSegment_072_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1566 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1566 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1566 13 14, g32p_row04_traceSegment_072_1566_0013, g32p_row04_traceSegment_072_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1593 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1593 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1593 13 14, g32p_row04_traceSegment_072_1593_0013, g32p_row04_traceSegment_072_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1566 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1566 27 27, g32p_row04_traceSegment_072_1566_0027, g32p_row04_traceSegment_072_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 1512 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1512 54 54, g32p_row04_traceSegment_072_1512_0054, g32p_row04_traceSegment_072_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1633 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1620 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1620 13 14, g32p_row04_traceSegment_072_1620_0013, g32p_row04_traceSegment_072_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1647 13 14, g32p_row04_traceSegment_072_1647_0013, g32p_row04_traceSegment_072_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1620 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1620 27 27, g32p_row04_traceSegment_072_1620_0027, g32p_row04_traceSegment_072_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1674 13 14, g32p_row04_traceSegment_072_1674_0013, g32p_row04_traceSegment_072_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_072 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_072 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_072_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_072 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1701 13 14, g32p_row04_traceSegment_072_1701_0013, g32p_row04_traceSegment_072_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_072 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1674 27 27, g32p_row04_traceSegment_072_1674_0027, g32p_row04_traceSegment_072_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_072 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1620 54 54, g32p_row04_traceSegment_072_1620_0054, g32p_row04_traceSegment_072_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_072 1512 216 = [1, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1512 108 108, g32p_row04_traceSegment_072_1512_0108, g32p_row04_traceSegment_072_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_072_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_072 1296 432 = [1, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 1296 216 216, g32p_row04_traceSegment_072_1296_0216, g32p_row04_traceSegment_072_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_072 864 864 = [1, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 864 432 432, g32p_row04_traceSegment_072_0864_0432, g32p_row04_traceSegment_072_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_072_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_072 0 1728 = [24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_072 0 864 864, g32p_row04_traceSegment_072_0000_0864, g32p_row04_traceSegment_072_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_072 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 72 = [24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_072_0000_1728

end HodgeLean.Foundations.Program

end
end
