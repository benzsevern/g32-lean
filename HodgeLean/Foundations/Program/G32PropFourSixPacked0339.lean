import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_045_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 0 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 0 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 0 13 14, g32p_row04_traceSegment_045_0000_0013, g32p_row04_traceSegment_045_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 27 13 14, g32p_row04_traceSegment_045_0027_0013, g32p_row04_traceSegment_045_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 0 27 27, g32p_row04_traceSegment_045_0000_0027, g32p_row04_traceSegment_045_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 67 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 54 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 54 13 14, g32p_row04_traceSegment_045_0054_0013, g32p_row04_traceSegment_045_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 81 13 14, g32p_row04_traceSegment_045_0081_0013, g32p_row04_traceSegment_045_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 54 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 54 27 27, g32p_row04_traceSegment_045_0054_0027, g32p_row04_traceSegment_045_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 0 108 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 0 54 54, g32p_row04_traceSegment_045_0000_0054, g32p_row04_traceSegment_045_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 108 13 14, g32p_row04_traceSegment_045_0108_0013, g32p_row04_traceSegment_045_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 135 13 14, g32p_row04_traceSegment_045_0135_0013, g32p_row04_traceSegment_045_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 108 27 27, g32p_row04_traceSegment_045_0108_0027, g32p_row04_traceSegment_045_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 162 13 14, g32p_row04_traceSegment_045_0162_0013, g32p_row04_traceSegment_045_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 189 13 14, g32p_row04_traceSegment_045_0189_0013, g32p_row04_traceSegment_045_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 162 27 27, g32p_row04_traceSegment_045_0162_0027, g32p_row04_traceSegment_045_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 108 54 54, g32p_row04_traceSegment_045_0108_0054, g32p_row04_traceSegment_045_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 0 216 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 0 108 108, g32p_row04_traceSegment_045_0000_0108, g32p_row04_traceSegment_045_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 216 13 14, g32p_row04_traceSegment_045_0216_0013, g32p_row04_traceSegment_045_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 243 13 14, g32p_row04_traceSegment_045_0243_0013, g32p_row04_traceSegment_045_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 216 27 27, g32p_row04_traceSegment_045_0216_0027, g32p_row04_traceSegment_045_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 270 13 14, g32p_row04_traceSegment_045_0270_0013, g32p_row04_traceSegment_045_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 297 13 14, g32p_row04_traceSegment_045_0297_0013, g32p_row04_traceSegment_045_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 270 27 27, g32p_row04_traceSegment_045_0270_0027, g32p_row04_traceSegment_045_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 216 54 54, g32p_row04_traceSegment_045_0216_0054, g32p_row04_traceSegment_045_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 324 13 14, g32p_row04_traceSegment_045_0324_0013, g32p_row04_traceSegment_045_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 351 13 14, g32p_row04_traceSegment_045_0351_0013, g32p_row04_traceSegment_045_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 324 27 27, g32p_row04_traceSegment_045_0324_0027, g32p_row04_traceSegment_045_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 378 13 14, g32p_row04_traceSegment_045_0378_0013, g32p_row04_traceSegment_045_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 405 13 14, g32p_row04_traceSegment_045_0405_0013, g32p_row04_traceSegment_045_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 378 27 27, g32p_row04_traceSegment_045_0378_0027, g32p_row04_traceSegment_045_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 324 54 54, g32p_row04_traceSegment_045_0324_0054, g32p_row04_traceSegment_045_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 216 108 108, g32p_row04_traceSegment_045_0216_0108, g32p_row04_traceSegment_045_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_045 0 432 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 0 216 216, g32p_row04_traceSegment_045_0000_0216, g32p_row04_traceSegment_045_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 432 13 14, g32p_row04_traceSegment_045_0432_0013, g32p_row04_traceSegment_045_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 459 13 14, g32p_row04_traceSegment_045_0459_0013, g32p_row04_traceSegment_045_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 432 27 27, g32p_row04_traceSegment_045_0432_0027, g32p_row04_traceSegment_045_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 486 13 14, g32p_row04_traceSegment_045_0486_0013, g32p_row04_traceSegment_045_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 513 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 526 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 513 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 513 13 14, g32p_row04_traceSegment_045_0513_0013, g32p_row04_traceSegment_045_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 486 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 486 27 27, g32p_row04_traceSegment_045_0486_0027, g32p_row04_traceSegment_045_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 432 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 432 54 54, g32p_row04_traceSegment_045_0432_0054, g32p_row04_traceSegment_045_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 540 13 14, g32p_row04_traceSegment_045_0540_0013, g32p_row04_traceSegment_045_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 567 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 567 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 567 13 14, g32p_row04_traceSegment_045_0567_0013, g32p_row04_traceSegment_045_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 540 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 540 27 27, g32p_row04_traceSegment_045_0540_0027, g32p_row04_traceSegment_045_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 594 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 607 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 594 27 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 594 13 14, g32p_row04_traceSegment_045_0594_0013, g32p_row04_traceSegment_045_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 621 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 621 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 621 13 14, g32p_row04_traceSegment_045_0621_0013, g32p_row04_traceSegment_045_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 594 54 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 594 27 27, g32p_row04_traceSegment_045_0594_0027, g32p_row04_traceSegment_045_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 540 108 = [4, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 540 54 54, g32p_row04_traceSegment_045_0540_0054, g32p_row04_traceSegment_045_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 432 216 = [4, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 432 108 108, g32p_row04_traceSegment_045_0432_0108, g32p_row04_traceSegment_045_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 648 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 661 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 648 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 648 13 14, g32p_row04_traceSegment_045_0648_0013, g32p_row04_traceSegment_045_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 675 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 688 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 675 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 675 13 14, g32p_row04_traceSegment_045_0675_0013, g32p_row04_traceSegment_045_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 648 54 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 648 27 27, g32p_row04_traceSegment_045_0648_0027, g32p_row04_traceSegment_045_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 715 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 702 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 702 13 14, g32p_row04_traceSegment_045_0702_0013, g32p_row04_traceSegment_045_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 729 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 742 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 729 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 729 13 14, g32p_row04_traceSegment_045_0729_0013, g32p_row04_traceSegment_045_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 702 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 702 27 27, g32p_row04_traceSegment_045_0702_0027, g32p_row04_traceSegment_045_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 648 108 = [0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 648 54 54, g32p_row04_traceSegment_045_0648_0054, g32p_row04_traceSegment_045_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 756 13 14, g32p_row04_traceSegment_045_0756_0013, g32p_row04_traceSegment_045_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 796 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 783 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 783 13 14, g32p_row04_traceSegment_045_0783_0013, g32p_row04_traceSegment_045_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 756 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 756 27 27, g32p_row04_traceSegment_045_0756_0027, g32p_row04_traceSegment_045_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 810 13 14, g32p_row04_traceSegment_045_0810_0013, g32p_row04_traceSegment_045_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 837 13 14, g32p_row04_traceSegment_045_0837_0013, g32p_row04_traceSegment_045_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 810 27 27, g32p_row04_traceSegment_045_0810_0027, g32p_row04_traceSegment_045_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 756 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 756 54 54, g32p_row04_traceSegment_045_0756_0054, g32p_row04_traceSegment_045_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 648 216 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 648 108 108, g32p_row04_traceSegment_045_0648_0108, g32p_row04_traceSegment_045_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_045 432 432 = [4, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 432 216 216, g32p_row04_traceSegment_045_0432_0216, g32p_row04_traceSegment_045_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_045 0 864 = [6, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 0 432 432, g32p_row04_traceSegment_045_0000_0432, g32p_row04_traceSegment_045_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 864 13 14, g32p_row04_traceSegment_045_0864_0013, g32p_row04_traceSegment_045_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 891 13 14, g32p_row04_traceSegment_045_0891_0013, g32p_row04_traceSegment_045_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 864 27 27, g32p_row04_traceSegment_045_0864_0027, g32p_row04_traceSegment_045_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 918 13 14, g32p_row04_traceSegment_045_0918_0013, g32p_row04_traceSegment_045_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 945 13 14, g32p_row04_traceSegment_045_0945_0013, g32p_row04_traceSegment_045_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 918 27 27, g32p_row04_traceSegment_045_0918_0027, g32p_row04_traceSegment_045_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 864 54 54, g32p_row04_traceSegment_045_0864_0054, g32p_row04_traceSegment_045_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 972 13 14, g32p_row04_traceSegment_045_0972_0013, g32p_row04_traceSegment_045_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 999 13 14, g32p_row04_traceSegment_045_0999_0013, g32p_row04_traceSegment_045_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 972 27 27, g32p_row04_traceSegment_045_0972_0027, g32p_row04_traceSegment_045_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1026 13 14, g32p_row04_traceSegment_045_1026_0013, g32p_row04_traceSegment_045_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1053 13 14, g32p_row04_traceSegment_045_1053_0013, g32p_row04_traceSegment_045_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1026 27 27, g32p_row04_traceSegment_045_1026_0027, g32p_row04_traceSegment_045_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 972 54 54, g32p_row04_traceSegment_045_0972_0054, g32p_row04_traceSegment_045_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 864 108 108, g32p_row04_traceSegment_045_0864_0108, g32p_row04_traceSegment_045_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1080 13 14, g32p_row04_traceSegment_045_1080_0013, g32p_row04_traceSegment_045_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1107 13 14, g32p_row04_traceSegment_045_1107_0013, g32p_row04_traceSegment_045_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1080 27 27, g32p_row04_traceSegment_045_1080_0027, g32p_row04_traceSegment_045_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1134 13 14, g32p_row04_traceSegment_045_1134_0013, g32p_row04_traceSegment_045_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1161 13 14, g32p_row04_traceSegment_045_1161_0013, g32p_row04_traceSegment_045_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1134 27 27, g32p_row04_traceSegment_045_1134_0027, g32p_row04_traceSegment_045_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1080 54 54, g32p_row04_traceSegment_045_1080_0054, g32p_row04_traceSegment_045_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1188 13 14, g32p_row04_traceSegment_045_1188_0013, g32p_row04_traceSegment_045_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1215 13 14, g32p_row04_traceSegment_045_1215_0013, g32p_row04_traceSegment_045_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1188 27 27, g32p_row04_traceSegment_045_1188_0027, g32p_row04_traceSegment_045_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1242 13 14, g32p_row04_traceSegment_045_1242_0013, g32p_row04_traceSegment_045_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1269 13 14, g32p_row04_traceSegment_045_1269_0013, g32p_row04_traceSegment_045_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1242 27 27, g32p_row04_traceSegment_045_1242_0027, g32p_row04_traceSegment_045_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1188 54 54, g32p_row04_traceSegment_045_1188_0054, g32p_row04_traceSegment_045_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1080 108 108, g32p_row04_traceSegment_045_1080_0108, g32p_row04_traceSegment_045_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_045 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 864 216 216, g32p_row04_traceSegment_045_0864_0216, g32p_row04_traceSegment_045_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1296 13 14, g32p_row04_traceSegment_045_1296_0013, g32p_row04_traceSegment_045_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1323 13 14, g32p_row04_traceSegment_045_1323_0013, g32p_row04_traceSegment_045_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1296 27 27, g32p_row04_traceSegment_045_1296_0027, g32p_row04_traceSegment_045_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1350 13 14, g32p_row04_traceSegment_045_1350_0013, g32p_row04_traceSegment_045_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1377 13 14, g32p_row04_traceSegment_045_1377_0013, g32p_row04_traceSegment_045_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1350 27 27, g32p_row04_traceSegment_045_1350_0027, g32p_row04_traceSegment_045_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1296 54 54, g32p_row04_traceSegment_045_1296_0054, g32p_row04_traceSegment_045_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1404 13 14, g32p_row04_traceSegment_045_1404_0013, g32p_row04_traceSegment_045_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1431 13 14, g32p_row04_traceSegment_045_1431_0013, g32p_row04_traceSegment_045_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1404 27 27, g32p_row04_traceSegment_045_1404_0027, g32p_row04_traceSegment_045_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1458 13 14, g32p_row04_traceSegment_045_1458_0013, g32p_row04_traceSegment_045_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1485 13 14, g32p_row04_traceSegment_045_1485_0013, g32p_row04_traceSegment_045_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1458 27 27, g32p_row04_traceSegment_045_1458_0027, g32p_row04_traceSegment_045_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1404 54 54, g32p_row04_traceSegment_045_1404_0054, g32p_row04_traceSegment_045_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1296 108 108, g32p_row04_traceSegment_045_1296_0108, g32p_row04_traceSegment_045_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1512 13 14, g32p_row04_traceSegment_045_1512_0013, g32p_row04_traceSegment_045_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1539 13 14, g32p_row04_traceSegment_045_1539_0013, g32p_row04_traceSegment_045_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1512 27 27, g32p_row04_traceSegment_045_1512_0027, g32p_row04_traceSegment_045_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1579 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1566 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1566 13 14, g32p_row04_traceSegment_045_1566_0013, g32p_row04_traceSegment_045_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1593 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1606 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1593 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1593 13 14, g32p_row04_traceSegment_045_1593_0013, g32p_row04_traceSegment_045_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1566 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1566 27 27, g32p_row04_traceSegment_045_1566_0027, g32p_row04_traceSegment_045_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 1512 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1512 54 54, g32p_row04_traceSegment_045_1512_0054, g32p_row04_traceSegment_045_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1620 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1633 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1620 27 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1620 13 14, g32p_row04_traceSegment_045_1620_0013, g32p_row04_traceSegment_045_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1647 13 14, g32p_row04_traceSegment_045_1647_0013, g32p_row04_traceSegment_045_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1620 54 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1620 27 27, g32p_row04_traceSegment_045_1620_0027, g32p_row04_traceSegment_045_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1674 13 14, g32p_row04_traceSegment_045_1674_0013, g32p_row04_traceSegment_045_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_045 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_045 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_045_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_045 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1701 13 14, g32p_row04_traceSegment_045_1701_0013, g32p_row04_traceSegment_045_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_045 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1674 27 27, g32p_row04_traceSegment_045_1674_0027, g32p_row04_traceSegment_045_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_045 1620 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1620 54 54, g32p_row04_traceSegment_045_1620_0054, g32p_row04_traceSegment_045_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_045 1512 216 = [10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1512 108 108, g32p_row04_traceSegment_045_1512_0108, g32p_row04_traceSegment_045_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_045_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_045 1296 432 = [10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 1296 216 216, g32p_row04_traceSegment_045_1296_0216, g32p_row04_traceSegment_045_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_045 864 864 = [10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 864 432 432, g32p_row04_traceSegment_045_0864_0432, g32p_row04_traceSegment_045_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_045_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_045 0 1728 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_045 0 864 864, g32p_row04_traceSegment_045_0000_0864, g32p_row04_traceSegment_045_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 45 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_045_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_048 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 48 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_048_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 0 13 14, g32p_row04_traceSegment_048_0000_0013, g32p_row04_traceSegment_048_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 27 13 14, g32p_row04_traceSegment_048_0027_0013, g32p_row04_traceSegment_048_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 0 27 27, g32p_row04_traceSegment_048_0000_0027, g32p_row04_traceSegment_048_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 54 13 14, g32p_row04_traceSegment_048_0054_0013, g32p_row04_traceSegment_048_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 81 13 14, g32p_row04_traceSegment_048_0081_0013, g32p_row04_traceSegment_048_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 54 27 27, g32p_row04_traceSegment_048_0054_0027, g32p_row04_traceSegment_048_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 0 54 54, g32p_row04_traceSegment_048_0000_0054, g32p_row04_traceSegment_048_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 108 13 14, g32p_row04_traceSegment_048_0108_0013, g32p_row04_traceSegment_048_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 135 13 14, g32p_row04_traceSegment_048_0135_0013, g32p_row04_traceSegment_048_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 108 27 27, g32p_row04_traceSegment_048_0108_0027, g32p_row04_traceSegment_048_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 175 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 162 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 162 13 14, g32p_row04_traceSegment_048_0162_0013, g32p_row04_traceSegment_048_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 202 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 189 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 189 13 14, g32p_row04_traceSegment_048_0189_0013, g32p_row04_traceSegment_048_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 162 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 162 27 27, g32p_row04_traceSegment_048_0162_0027, g32p_row04_traceSegment_048_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 108 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 108 54 54, g32p_row04_traceSegment_048_0108_0054, g32p_row04_traceSegment_048_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 0 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 0 108 108, g32p_row04_traceSegment_048_0000_0108, g32p_row04_traceSegment_048_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 216 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 216 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 216 13 14, g32p_row04_traceSegment_048_0216_0013, g32p_row04_traceSegment_048_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 243 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 256 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 243 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 243 13 14, g32p_row04_traceSegment_048_0243_0013, g32p_row04_traceSegment_048_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 216 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 216 27 27, g32p_row04_traceSegment_048_0216_0027, g32p_row04_traceSegment_048_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 270 13 14, g32p_row04_traceSegment_048_0270_0013, g32p_row04_traceSegment_048_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 297 13 14, g32p_row04_traceSegment_048_0297_0013, g32p_row04_traceSegment_048_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 270 27 27, g32p_row04_traceSegment_048_0270_0027, g32p_row04_traceSegment_048_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 216 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 216 54 54, g32p_row04_traceSegment_048_0216_0054, g32p_row04_traceSegment_048_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 324 13 14, g32p_row04_traceSegment_048_0324_0013, g32p_row04_traceSegment_048_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 351 13 14, g32p_row04_traceSegment_048_0351_0013, g32p_row04_traceSegment_048_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 324 27 27, g32p_row04_traceSegment_048_0324_0027, g32p_row04_traceSegment_048_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 378 13 14, g32p_row04_traceSegment_048_0378_0013, g32p_row04_traceSegment_048_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 405 13 14, g32p_row04_traceSegment_048_0405_0013, g32p_row04_traceSegment_048_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 378 27 27, g32p_row04_traceSegment_048_0378_0027, g32p_row04_traceSegment_048_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 324 54 54, g32p_row04_traceSegment_048_0324_0054, g32p_row04_traceSegment_048_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 216 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 216 108 108, g32p_row04_traceSegment_048_0216_0108, g32p_row04_traceSegment_048_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_048 0 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 0 216 216, g32p_row04_traceSegment_048_0000_0216, g32p_row04_traceSegment_048_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 432 13 14, g32p_row04_traceSegment_048_0432_0013, g32p_row04_traceSegment_048_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 459 13 14, g32p_row04_traceSegment_048_0459_0013, g32p_row04_traceSegment_048_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 432 27 27, g32p_row04_traceSegment_048_0432_0027, g32p_row04_traceSegment_048_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 486 13 14, g32p_row04_traceSegment_048_0486_0013, g32p_row04_traceSegment_048_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 513 13 14, g32p_row04_traceSegment_048_0513_0013, g32p_row04_traceSegment_048_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 486 27 27, g32p_row04_traceSegment_048_0486_0027, g32p_row04_traceSegment_048_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 432 54 54, g32p_row04_traceSegment_048_0432_0054, g32p_row04_traceSegment_048_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 540 13 14, g32p_row04_traceSegment_048_0540_0013, g32p_row04_traceSegment_048_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 567 13 14, g32p_row04_traceSegment_048_0567_0013, g32p_row04_traceSegment_048_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 540 27 27, g32p_row04_traceSegment_048_0540_0027, g32p_row04_traceSegment_048_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 594 13 14, g32p_row04_traceSegment_048_0594_0013, g32p_row04_traceSegment_048_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 621 13 14, g32p_row04_traceSegment_048_0621_0013, g32p_row04_traceSegment_048_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 594 27 27, g32p_row04_traceSegment_048_0594_0027, g32p_row04_traceSegment_048_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 540 54 54, g32p_row04_traceSegment_048_0540_0054, g32p_row04_traceSegment_048_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 432 108 108, g32p_row04_traceSegment_048_0432_0108, g32p_row04_traceSegment_048_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 648 13 14, g32p_row04_traceSegment_048_0648_0013, g32p_row04_traceSegment_048_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 675 13 14, g32p_row04_traceSegment_048_0675_0013, g32p_row04_traceSegment_048_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 648 27 27, g32p_row04_traceSegment_048_0648_0027, g32p_row04_traceSegment_048_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 702 13 14, g32p_row04_traceSegment_048_0702_0013, g32p_row04_traceSegment_048_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 729 13 14, g32p_row04_traceSegment_048_0729_0013, g32p_row04_traceSegment_048_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 702 27 27, g32p_row04_traceSegment_048_0702_0027, g32p_row04_traceSegment_048_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 648 54 54, g32p_row04_traceSegment_048_0648_0054, g32p_row04_traceSegment_048_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 756 13 14, g32p_row04_traceSegment_048_0756_0013, g32p_row04_traceSegment_048_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 783 13 14, g32p_row04_traceSegment_048_0783_0013, g32p_row04_traceSegment_048_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 756 27 27, g32p_row04_traceSegment_048_0756_0027, g32p_row04_traceSegment_048_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 810 13 14, g32p_row04_traceSegment_048_0810_0013, g32p_row04_traceSegment_048_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 837 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 850 14 = [1, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 837 27 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 837 13 14, g32p_row04_traceSegment_048_0837_0013, g32p_row04_traceSegment_048_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 810 54 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 810 27 27, g32p_row04_traceSegment_048_0810_0027, g32p_row04_traceSegment_048_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 756 108 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 756 54 54, g32p_row04_traceSegment_048_0756_0054, g32p_row04_traceSegment_048_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 648 216 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 648 108 108, g32p_row04_traceSegment_048_0648_0108, g32p_row04_traceSegment_048_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_048 432 432 = [1, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 432 216 216, g32p_row04_traceSegment_048_0432_0216, g32p_row04_traceSegment_048_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_048 0 864 = [7, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 0 432 432, g32p_row04_traceSegment_048_0000_0432, g32p_row04_traceSegment_048_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 864 13 = [4, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 877 14 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 864 27 = [5, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 864 13 14, g32p_row04_traceSegment_048_0864_0013, g32p_row04_traceSegment_048_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 891 13 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 904 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 891 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 891 13 14, g32p_row04_traceSegment_048_0891_0013, g32p_row04_traceSegment_048_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 864 54 = [9, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 864 27 27, g32p_row04_traceSegment_048_0864_0027, g32p_row04_traceSegment_048_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 918 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 918 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 918 13 14, g32p_row04_traceSegment_048_0918_0013, g32p_row04_traceSegment_048_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 945 13 14, g32p_row04_traceSegment_048_0945_0013, g32p_row04_traceSegment_048_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 918 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 918 27 27, g32p_row04_traceSegment_048_0918_0027, g32p_row04_traceSegment_048_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 864 108 = [10, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 864 54 54, g32p_row04_traceSegment_048_0864_0054, g32p_row04_traceSegment_048_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 972 13 14, g32p_row04_traceSegment_048_0972_0013, g32p_row04_traceSegment_048_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 999 13 14, g32p_row04_traceSegment_048_0999_0013, g32p_row04_traceSegment_048_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 972 27 27, g32p_row04_traceSegment_048_0972_0027, g32p_row04_traceSegment_048_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1026 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1039 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1026 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1026 13 14, g32p_row04_traceSegment_048_1026_0013, g32p_row04_traceSegment_048_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1053 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1053 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1053 13 14, g32p_row04_traceSegment_048_1053_0013, g32p_row04_traceSegment_048_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1026 54 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1026 27 27, g32p_row04_traceSegment_048_1026_0027, g32p_row04_traceSegment_048_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 972 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 972 54 54, g32p_row04_traceSegment_048_0972_0054, g32p_row04_traceSegment_048_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 864 216 = [10, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 864 108 108, g32p_row04_traceSegment_048_0864_0108, g32p_row04_traceSegment_048_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1080 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1080 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1080 13 14, g32p_row04_traceSegment_048_1080_0013, g32p_row04_traceSegment_048_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1107 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1120 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1107 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1107 13 14, g32p_row04_traceSegment_048_1107_0013, g32p_row04_traceSegment_048_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1080 54 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1080 27 27, g32p_row04_traceSegment_048_1080_0027, g32p_row04_traceSegment_048_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1134 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1147 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1134 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1134 13 14, g32p_row04_traceSegment_048_1134_0013, g32p_row04_traceSegment_048_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1161 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1174 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1161 27 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1161 13 14, g32p_row04_traceSegment_048_1161_0013, g32p_row04_traceSegment_048_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1134 54 = [2, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1134 27 27, g32p_row04_traceSegment_048_1134_0027, g32p_row04_traceSegment_048_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 1080 108 = [2, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1080 54 54, g32p_row04_traceSegment_048_1080_0054, g32p_row04_traceSegment_048_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1188 13 = [1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1201 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1188 27 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1188 13 14, g32p_row04_traceSegment_048_1188_0013, g32p_row04_traceSegment_048_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1215 13 14, g32p_row04_traceSegment_048_1215_0013, g32p_row04_traceSegment_048_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1188 54 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1188 27 27, g32p_row04_traceSegment_048_1188_0027, g32p_row04_traceSegment_048_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1242 13 14, g32p_row04_traceSegment_048_1242_0013, g32p_row04_traceSegment_048_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1269 13 14, g32p_row04_traceSegment_048_1269_0013, g32p_row04_traceSegment_048_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1242 27 27, g32p_row04_traceSegment_048_1242_0027, g32p_row04_traceSegment_048_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 1188 108 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1188 54 54, g32p_row04_traceSegment_048_1188_0054, g32p_row04_traceSegment_048_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 1080 216 = [4, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1080 108 108, g32p_row04_traceSegment_048_1080_0108, g32p_row04_traceSegment_048_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_048 864 432 = [14, 21] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 864 216 216, g32p_row04_traceSegment_048_0864_0216, g32p_row04_traceSegment_048_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1296 13 14, g32p_row04_traceSegment_048_1296_0013, g32p_row04_traceSegment_048_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1323 13 14, g32p_row04_traceSegment_048_1323_0013, g32p_row04_traceSegment_048_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1296 27 27, g32p_row04_traceSegment_048_1296_0027, g32p_row04_traceSegment_048_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1350 13 14, g32p_row04_traceSegment_048_1350_0013, g32p_row04_traceSegment_048_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1377 13 14, g32p_row04_traceSegment_048_1377_0013, g32p_row04_traceSegment_048_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1350 27 27, g32p_row04_traceSegment_048_1350_0027, g32p_row04_traceSegment_048_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1296 54 54, g32p_row04_traceSegment_048_1296_0054, g32p_row04_traceSegment_048_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1404 13 14, g32p_row04_traceSegment_048_1404_0013, g32p_row04_traceSegment_048_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1431 13 14, g32p_row04_traceSegment_048_1431_0013, g32p_row04_traceSegment_048_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1404 27 27, g32p_row04_traceSegment_048_1404_0027, g32p_row04_traceSegment_048_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1458 13 14, g32p_row04_traceSegment_048_1458_0013, g32p_row04_traceSegment_048_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1485 13 14, g32p_row04_traceSegment_048_1485_0013, g32p_row04_traceSegment_048_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1458 27 27, g32p_row04_traceSegment_048_1458_0027, g32p_row04_traceSegment_048_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1404 54 54, g32p_row04_traceSegment_048_1404_0054, g32p_row04_traceSegment_048_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1296 108 108, g32p_row04_traceSegment_048_1296_0108, g32p_row04_traceSegment_048_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1512 13 14, g32p_row04_traceSegment_048_1512_0013, g32p_row04_traceSegment_048_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1539 13 14, g32p_row04_traceSegment_048_1539_0013, g32p_row04_traceSegment_048_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1512 27 27, g32p_row04_traceSegment_048_1512_0027, g32p_row04_traceSegment_048_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1566 13 14, g32p_row04_traceSegment_048_1566_0013, g32p_row04_traceSegment_048_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1593 13 14, g32p_row04_traceSegment_048_1593_0013, g32p_row04_traceSegment_048_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1566 27 27, g32p_row04_traceSegment_048_1566_0027, g32p_row04_traceSegment_048_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1512 54 54, g32p_row04_traceSegment_048_1512_0054, g32p_row04_traceSegment_048_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1620 13 14, g32p_row04_traceSegment_048_1620_0013, g32p_row04_traceSegment_048_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1647 13 14, g32p_row04_traceSegment_048_1647_0013, g32p_row04_traceSegment_048_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1620 27 27, g32p_row04_traceSegment_048_1620_0027, g32p_row04_traceSegment_048_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1674 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1674 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1674 13 14, g32p_row04_traceSegment_048_1674_0013, g32p_row04_traceSegment_048_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_048 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_048 1714 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_048_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_048 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1701 13 14, g32p_row04_traceSegment_048_1701_0013, g32p_row04_traceSegment_048_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_048 1674 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1674 27 27, g32p_row04_traceSegment_048_1674_0027, g32p_row04_traceSegment_048_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_048 1620 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1620 54 54, g32p_row04_traceSegment_048_1620_0054, g32p_row04_traceSegment_048_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_048 1512 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1512 108 108, g32p_row04_traceSegment_048_1512_0108, g32p_row04_traceSegment_048_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_048_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_048 1296 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 1296 216 216, g32p_row04_traceSegment_048_1296_0216, g32p_row04_traceSegment_048_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_048 864 864 = [17, 21] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 864 432 432, g32p_row04_traceSegment_048_0864_0432, g32p_row04_traceSegment_048_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_048_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_048 0 1728 = [24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_048 0 864 864, g32p_row04_traceSegment_048_0000_0864, g32p_row04_traceSegment_048_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_048 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 48 = [24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_048_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_050 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 50 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_050_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 0 13 14, g32p_row04_traceSegment_050_0000_0013, g32p_row04_traceSegment_050_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 27 13 14, g32p_row04_traceSegment_050_0027_0013, g32p_row04_traceSegment_050_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 0 27 27, g32p_row04_traceSegment_050_0000_0027, g32p_row04_traceSegment_050_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 54 13 14, g32p_row04_traceSegment_050_0054_0013, g32p_row04_traceSegment_050_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 81 13 14, g32p_row04_traceSegment_050_0081_0013, g32p_row04_traceSegment_050_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 54 27 27, g32p_row04_traceSegment_050_0054_0027, g32p_row04_traceSegment_050_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 0 54 54, g32p_row04_traceSegment_050_0000_0054, g32p_row04_traceSegment_050_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 108 13 14, g32p_row04_traceSegment_050_0108_0013, g32p_row04_traceSegment_050_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 135 13 14, g32p_row04_traceSegment_050_0135_0013, g32p_row04_traceSegment_050_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 108 27 27, g32p_row04_traceSegment_050_0108_0027, g32p_row04_traceSegment_050_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 162 13 14, g32p_row04_traceSegment_050_0162_0013, g32p_row04_traceSegment_050_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 189 13 14, g32p_row04_traceSegment_050_0189_0013, g32p_row04_traceSegment_050_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 162 27 27, g32p_row04_traceSegment_050_0162_0027, g32p_row04_traceSegment_050_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 108 54 54, g32p_row04_traceSegment_050_0108_0054, g32p_row04_traceSegment_050_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 0 108 108, g32p_row04_traceSegment_050_0000_0108, g32p_row04_traceSegment_050_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 216 13 14, g32p_row04_traceSegment_050_0216_0013, g32p_row04_traceSegment_050_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 243 13 14, g32p_row04_traceSegment_050_0243_0013, g32p_row04_traceSegment_050_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 216 27 27, g32p_row04_traceSegment_050_0216_0027, g32p_row04_traceSegment_050_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 270 13 14, g32p_row04_traceSegment_050_0270_0013, g32p_row04_traceSegment_050_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 297 13 14, g32p_row04_traceSegment_050_0297_0013, g32p_row04_traceSegment_050_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 270 27 27, g32p_row04_traceSegment_050_0270_0027, g32p_row04_traceSegment_050_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 216 54 54, g32p_row04_traceSegment_050_0216_0054, g32p_row04_traceSegment_050_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 324 13 14, g32p_row04_traceSegment_050_0324_0013, g32p_row04_traceSegment_050_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 351 13 14, g32p_row04_traceSegment_050_0351_0013, g32p_row04_traceSegment_050_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 324 27 27, g32p_row04_traceSegment_050_0324_0027, g32p_row04_traceSegment_050_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 378 13 14, g32p_row04_traceSegment_050_0378_0013, g32p_row04_traceSegment_050_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 405 13 14, g32p_row04_traceSegment_050_0405_0013, g32p_row04_traceSegment_050_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 378 27 27, g32p_row04_traceSegment_050_0378_0027, g32p_row04_traceSegment_050_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 324 54 54, g32p_row04_traceSegment_050_0324_0054, g32p_row04_traceSegment_050_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 216 108 108, g32p_row04_traceSegment_050_0216_0108, g32p_row04_traceSegment_050_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_050 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 0 216 216, g32p_row04_traceSegment_050_0000_0216, g32p_row04_traceSegment_050_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 432 13 14, g32p_row04_traceSegment_050_0432_0013, g32p_row04_traceSegment_050_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 459 13 14, g32p_row04_traceSegment_050_0459_0013, g32p_row04_traceSegment_050_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 432 27 27, g32p_row04_traceSegment_050_0432_0027, g32p_row04_traceSegment_050_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 486 13 14, g32p_row04_traceSegment_050_0486_0013, g32p_row04_traceSegment_050_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 513 13 14, g32p_row04_traceSegment_050_0513_0013, g32p_row04_traceSegment_050_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 486 27 27, g32p_row04_traceSegment_050_0486_0027, g32p_row04_traceSegment_050_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 432 54 54, g32p_row04_traceSegment_050_0432_0054, g32p_row04_traceSegment_050_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 540 13 14, g32p_row04_traceSegment_050_0540_0013, g32p_row04_traceSegment_050_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 567 13 14, g32p_row04_traceSegment_050_0567_0013, g32p_row04_traceSegment_050_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 540 27 27, g32p_row04_traceSegment_050_0540_0027, g32p_row04_traceSegment_050_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 594 13 14, g32p_row04_traceSegment_050_0594_0013, g32p_row04_traceSegment_050_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 621 13 14, g32p_row04_traceSegment_050_0621_0013, g32p_row04_traceSegment_050_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 594 27 27, g32p_row04_traceSegment_050_0594_0027, g32p_row04_traceSegment_050_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 540 54 54, g32p_row04_traceSegment_050_0540_0054, g32p_row04_traceSegment_050_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 432 108 108, g32p_row04_traceSegment_050_0432_0108, g32p_row04_traceSegment_050_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 648 13 14, g32p_row04_traceSegment_050_0648_0013, g32p_row04_traceSegment_050_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 675 13 14, g32p_row04_traceSegment_050_0675_0013, g32p_row04_traceSegment_050_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 648 27 27, g32p_row04_traceSegment_050_0648_0027, g32p_row04_traceSegment_050_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 702 13 14, g32p_row04_traceSegment_050_0702_0013, g32p_row04_traceSegment_050_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 729 13 14, g32p_row04_traceSegment_050_0729_0013, g32p_row04_traceSegment_050_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 702 27 27, g32p_row04_traceSegment_050_0702_0027, g32p_row04_traceSegment_050_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 648 54 54, g32p_row04_traceSegment_050_0648_0054, g32p_row04_traceSegment_050_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 756 13 14, g32p_row04_traceSegment_050_0756_0013, g32p_row04_traceSegment_050_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 783 13 14, g32p_row04_traceSegment_050_0783_0013, g32p_row04_traceSegment_050_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 756 27 27, g32p_row04_traceSegment_050_0756_0027, g32p_row04_traceSegment_050_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 810 13 14, g32p_row04_traceSegment_050_0810_0013, g32p_row04_traceSegment_050_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 837 13 14, g32p_row04_traceSegment_050_0837_0013, g32p_row04_traceSegment_050_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 810 27 27, g32p_row04_traceSegment_050_0810_0027, g32p_row04_traceSegment_050_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 756 54 54, g32p_row04_traceSegment_050_0756_0054, g32p_row04_traceSegment_050_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 648 108 108, g32p_row04_traceSegment_050_0648_0108, g32p_row04_traceSegment_050_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_050 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 432 216 216, g32p_row04_traceSegment_050_0432_0216, g32p_row04_traceSegment_050_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_050 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 0 432 432, g32p_row04_traceSegment_050_0000_0432, g32p_row04_traceSegment_050_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 864 13 14, g32p_row04_traceSegment_050_0864_0013, g32p_row04_traceSegment_050_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 891 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 904 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 891 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 891 13 14, g32p_row04_traceSegment_050_0891_0013, g32p_row04_traceSegment_050_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 864 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 864 27 27, g32p_row04_traceSegment_050_0864_0027, g32p_row04_traceSegment_050_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 918 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 931 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 918 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 918 13 14, g32p_row04_traceSegment_050_0918_0013, g32p_row04_traceSegment_050_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 945 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 958 14 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 945 27 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 945 13 14, g32p_row04_traceSegment_050_0945_0013, g32p_row04_traceSegment_050_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 918 54 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 918 27 27, g32p_row04_traceSegment_050_0918_0027, g32p_row04_traceSegment_050_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 864 108 = [0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 864 54 54, g32p_row04_traceSegment_050_0864_0054, g32p_row04_traceSegment_050_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 972 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 985 14 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 972 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 972 13 14, g32p_row04_traceSegment_050_0972_0013, g32p_row04_traceSegment_050_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 999 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1012 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 999 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 999 13 14, g32p_row04_traceSegment_050_0999_0013, g32p_row04_traceSegment_050_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 972 54 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 972 27 27, g32p_row04_traceSegment_050_0972_0027, g32p_row04_traceSegment_050_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1039 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1026 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1026 13 14, g32p_row04_traceSegment_050_1026_0013, g32p_row04_traceSegment_050_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1053 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1053 13 14, g32p_row04_traceSegment_050_1053_0013, g32p_row04_traceSegment_050_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1026 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1026 27 27, g32p_row04_traceSegment_050_1026_0027, g32p_row04_traceSegment_050_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 972 108 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 972 54 54, g32p_row04_traceSegment_050_0972_0054, g32p_row04_traceSegment_050_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 864 216 = [0, 0, 23] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 864 108 108, g32p_row04_traceSegment_050_0864_0108, g32p_row04_traceSegment_050_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1093 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1080 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1080 13 14, g32p_row04_traceSegment_050_1080_0013, g32p_row04_traceSegment_050_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1107 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1107 13 14, g32p_row04_traceSegment_050_1107_0013, g32p_row04_traceSegment_050_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1080 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1080 27 27, g32p_row04_traceSegment_050_1080_0027, g32p_row04_traceSegment_050_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1134 13 14, g32p_row04_traceSegment_050_1134_0013, g32p_row04_traceSegment_050_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1161 13 14, g32p_row04_traceSegment_050_1161_0013, g32p_row04_traceSegment_050_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1134 27 27, g32p_row04_traceSegment_050_1134_0027, g32p_row04_traceSegment_050_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 1080 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1080 54 54, g32p_row04_traceSegment_050_1080_0054, g32p_row04_traceSegment_050_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1188 13 14, g32p_row04_traceSegment_050_1188_0013, g32p_row04_traceSegment_050_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1215 13 14, g32p_row04_traceSegment_050_1215_0013, g32p_row04_traceSegment_050_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1188 27 27, g32p_row04_traceSegment_050_1188_0027, g32p_row04_traceSegment_050_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1242 13 14, g32p_row04_traceSegment_050_1242_0013, g32p_row04_traceSegment_050_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1269 13 14, g32p_row04_traceSegment_050_1269_0013, g32p_row04_traceSegment_050_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1242 27 27, g32p_row04_traceSegment_050_1242_0027, g32p_row04_traceSegment_050_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1188 54 54, g32p_row04_traceSegment_050_1188_0054, g32p_row04_traceSegment_050_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 1080 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1080 108 108, g32p_row04_traceSegment_050_1080_0108, g32p_row04_traceSegment_050_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_050 864 432 = [0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 864 216 216, g32p_row04_traceSegment_050_0864_0216, g32p_row04_traceSegment_050_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1296 13 14, g32p_row04_traceSegment_050_1296_0013, g32p_row04_traceSegment_050_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1323 13 14, g32p_row04_traceSegment_050_1323_0013, g32p_row04_traceSegment_050_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1296 27 27, g32p_row04_traceSegment_050_1296_0027, g32p_row04_traceSegment_050_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1350 13 14, g32p_row04_traceSegment_050_1350_0013, g32p_row04_traceSegment_050_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1377 13 14, g32p_row04_traceSegment_050_1377_0013, g32p_row04_traceSegment_050_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1350 27 27, g32p_row04_traceSegment_050_1350_0027, g32p_row04_traceSegment_050_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1296 54 54, g32p_row04_traceSegment_050_1296_0054, g32p_row04_traceSegment_050_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1404 13 14, g32p_row04_traceSegment_050_1404_0013, g32p_row04_traceSegment_050_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1431 13 14, g32p_row04_traceSegment_050_1431_0013, g32p_row04_traceSegment_050_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1404 27 27, g32p_row04_traceSegment_050_1404_0027, g32p_row04_traceSegment_050_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1458 13 14, g32p_row04_traceSegment_050_1458_0013, g32p_row04_traceSegment_050_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1485 13 14, g32p_row04_traceSegment_050_1485_0013, g32p_row04_traceSegment_050_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1458 27 27, g32p_row04_traceSegment_050_1458_0027, g32p_row04_traceSegment_050_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1404 54 54, g32p_row04_traceSegment_050_1404_0054, g32p_row04_traceSegment_050_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1296 108 108, g32p_row04_traceSegment_050_1296_0108, g32p_row04_traceSegment_050_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1512 13 14, g32p_row04_traceSegment_050_1512_0013, g32p_row04_traceSegment_050_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1539 13 14, g32p_row04_traceSegment_050_1539_0013, g32p_row04_traceSegment_050_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1512 27 27, g32p_row04_traceSegment_050_1512_0027, g32p_row04_traceSegment_050_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1566 13 14, g32p_row04_traceSegment_050_1566_0013, g32p_row04_traceSegment_050_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1593 13 14, g32p_row04_traceSegment_050_1593_0013, g32p_row04_traceSegment_050_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1566 27 27, g32p_row04_traceSegment_050_1566_0027, g32p_row04_traceSegment_050_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1512 54 54, g32p_row04_traceSegment_050_1512_0054, g32p_row04_traceSegment_050_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1620 13 14, g32p_row04_traceSegment_050_1620_0013, g32p_row04_traceSegment_050_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1647 13 14, g32p_row04_traceSegment_050_1647_0013, g32p_row04_traceSegment_050_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1620 27 27, g32p_row04_traceSegment_050_1620_0027, g32p_row04_traceSegment_050_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1687 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1674 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1674 13 14, g32p_row04_traceSegment_050_1674_0013, g32p_row04_traceSegment_050_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_050 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_050 1714 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_050_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_050 1701 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1701 13 14, g32p_row04_traceSegment_050_1701_0013, g32p_row04_traceSegment_050_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_050 1674 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1674 27 27, g32p_row04_traceSegment_050_1674_0027, g32p_row04_traceSegment_050_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_050 1620 108 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1620 54 54, g32p_row04_traceSegment_050_1620_0054, g32p_row04_traceSegment_050_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_050 1512 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1512 108 108, g32p_row04_traceSegment_050_1512_0108, g32p_row04_traceSegment_050_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_050_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_050 1296 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 1296 216 216, g32p_row04_traceSegment_050_1296_0216, g32p_row04_traceSegment_050_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_050 864 864 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 864 432 432, g32p_row04_traceSegment_050_0864_0432, g32p_row04_traceSegment_050_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_050_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_050 0 1728 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_050 0 864 864, g32p_row04_traceSegment_050_0000_0864, g32p_row04_traceSegment_050_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_050 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 50 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_050_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_051 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 51 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_051_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 0 13 14, g32p_row04_traceSegment_051_0000_0013, g32p_row04_traceSegment_051_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 27 13 14, g32p_row04_traceSegment_051_0027_0013, g32p_row04_traceSegment_051_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 0 27 27, g32p_row04_traceSegment_051_0000_0027, g32p_row04_traceSegment_051_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 54 13 14, g32p_row04_traceSegment_051_0054_0013, g32p_row04_traceSegment_051_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 81 13 14, g32p_row04_traceSegment_051_0081_0013, g32p_row04_traceSegment_051_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 54 27 27, g32p_row04_traceSegment_051_0054_0027, g32p_row04_traceSegment_051_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 0 54 54, g32p_row04_traceSegment_051_0000_0054, g32p_row04_traceSegment_051_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 108 13 14, g32p_row04_traceSegment_051_0108_0013, g32p_row04_traceSegment_051_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 135 13 14, g32p_row04_traceSegment_051_0135_0013, g32p_row04_traceSegment_051_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 108 27 27, g32p_row04_traceSegment_051_0108_0027, g32p_row04_traceSegment_051_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 162 13 14, g32p_row04_traceSegment_051_0162_0013, g32p_row04_traceSegment_051_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 189 13 14, g32p_row04_traceSegment_051_0189_0013, g32p_row04_traceSegment_051_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 162 27 27, g32p_row04_traceSegment_051_0162_0027, g32p_row04_traceSegment_051_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 108 54 54, g32p_row04_traceSegment_051_0108_0054, g32p_row04_traceSegment_051_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 0 108 108, g32p_row04_traceSegment_051_0000_0108, g32p_row04_traceSegment_051_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 216 13 14, g32p_row04_traceSegment_051_0216_0013, g32p_row04_traceSegment_051_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 243 13 14, g32p_row04_traceSegment_051_0243_0013, g32p_row04_traceSegment_051_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 216 27 27, g32p_row04_traceSegment_051_0216_0027, g32p_row04_traceSegment_051_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 270 13 14, g32p_row04_traceSegment_051_0270_0013, g32p_row04_traceSegment_051_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 297 13 14, g32p_row04_traceSegment_051_0297_0013, g32p_row04_traceSegment_051_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 270 27 27, g32p_row04_traceSegment_051_0270_0027, g32p_row04_traceSegment_051_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 216 54 54, g32p_row04_traceSegment_051_0216_0054, g32p_row04_traceSegment_051_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 324 13 14, g32p_row04_traceSegment_051_0324_0013, g32p_row04_traceSegment_051_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 351 13 14, g32p_row04_traceSegment_051_0351_0013, g32p_row04_traceSegment_051_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 324 27 27, g32p_row04_traceSegment_051_0324_0027, g32p_row04_traceSegment_051_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 378 13 14, g32p_row04_traceSegment_051_0378_0013, g32p_row04_traceSegment_051_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 405 13 14, g32p_row04_traceSegment_051_0405_0013, g32p_row04_traceSegment_051_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 378 27 27, g32p_row04_traceSegment_051_0378_0027, g32p_row04_traceSegment_051_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 324 54 54, g32p_row04_traceSegment_051_0324_0054, g32p_row04_traceSegment_051_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 216 108 108, g32p_row04_traceSegment_051_0216_0108, g32p_row04_traceSegment_051_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_051 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 0 216 216, g32p_row04_traceSegment_051_0000_0216, g32p_row04_traceSegment_051_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 432 13 14, g32p_row04_traceSegment_051_0432_0013, g32p_row04_traceSegment_051_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 459 13 14, g32p_row04_traceSegment_051_0459_0013, g32p_row04_traceSegment_051_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 432 27 27, g32p_row04_traceSegment_051_0432_0027, g32p_row04_traceSegment_051_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 486 13 14, g32p_row04_traceSegment_051_0486_0013, g32p_row04_traceSegment_051_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 513 13 14, g32p_row04_traceSegment_051_0513_0013, g32p_row04_traceSegment_051_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 486 27 27, g32p_row04_traceSegment_051_0486_0027, g32p_row04_traceSegment_051_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 432 54 54, g32p_row04_traceSegment_051_0432_0054, g32p_row04_traceSegment_051_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 540 13 14, g32p_row04_traceSegment_051_0540_0013, g32p_row04_traceSegment_051_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 567 13 14, g32p_row04_traceSegment_051_0567_0013, g32p_row04_traceSegment_051_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 540 27 27, g32p_row04_traceSegment_051_0540_0027, g32p_row04_traceSegment_051_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 594 13 14, g32p_row04_traceSegment_051_0594_0013, g32p_row04_traceSegment_051_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 621 13 14, g32p_row04_traceSegment_051_0621_0013, g32p_row04_traceSegment_051_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 594 27 27, g32p_row04_traceSegment_051_0594_0027, g32p_row04_traceSegment_051_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 540 54 54, g32p_row04_traceSegment_051_0540_0054, g32p_row04_traceSegment_051_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 432 108 108, g32p_row04_traceSegment_051_0432_0108, g32p_row04_traceSegment_051_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 648 13 14, g32p_row04_traceSegment_051_0648_0013, g32p_row04_traceSegment_051_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 675 13 14, g32p_row04_traceSegment_051_0675_0013, g32p_row04_traceSegment_051_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 648 27 27, g32p_row04_traceSegment_051_0648_0027, g32p_row04_traceSegment_051_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 702 13 14, g32p_row04_traceSegment_051_0702_0013, g32p_row04_traceSegment_051_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 729 13 14, g32p_row04_traceSegment_051_0729_0013, g32p_row04_traceSegment_051_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 702 27 27, g32p_row04_traceSegment_051_0702_0027, g32p_row04_traceSegment_051_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 648 54 54, g32p_row04_traceSegment_051_0648_0054, g32p_row04_traceSegment_051_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 756 13 14, g32p_row04_traceSegment_051_0756_0013, g32p_row04_traceSegment_051_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 783 13 14, g32p_row04_traceSegment_051_0783_0013, g32p_row04_traceSegment_051_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 756 27 27, g32p_row04_traceSegment_051_0756_0027, g32p_row04_traceSegment_051_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 810 13 14, g32p_row04_traceSegment_051_0810_0013, g32p_row04_traceSegment_051_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 837 13 14, g32p_row04_traceSegment_051_0837_0013, g32p_row04_traceSegment_051_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 810 27 27, g32p_row04_traceSegment_051_0810_0027, g32p_row04_traceSegment_051_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 756 54 54, g32p_row04_traceSegment_051_0756_0054, g32p_row04_traceSegment_051_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 648 108 108, g32p_row04_traceSegment_051_0648_0108, g32p_row04_traceSegment_051_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_051 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 432 216 216, g32p_row04_traceSegment_051_0432_0216, g32p_row04_traceSegment_051_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_051 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 0 432 432, g32p_row04_traceSegment_051_0000_0432, g32p_row04_traceSegment_051_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 864 13 14, g32p_row04_traceSegment_051_0864_0013, g32p_row04_traceSegment_051_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 891 13 14, g32p_row04_traceSegment_051_0891_0013, g32p_row04_traceSegment_051_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 864 27 27, g32p_row04_traceSegment_051_0864_0027, g32p_row04_traceSegment_051_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 918 13 14, g32p_row04_traceSegment_051_0918_0013, g32p_row04_traceSegment_051_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 945 13 14, g32p_row04_traceSegment_051_0945_0013, g32p_row04_traceSegment_051_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 918 27 27, g32p_row04_traceSegment_051_0918_0027, g32p_row04_traceSegment_051_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 864 54 54, g32p_row04_traceSegment_051_0864_0054, g32p_row04_traceSegment_051_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 972 13 14, g32p_row04_traceSegment_051_0972_0013, g32p_row04_traceSegment_051_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 999 13 14, g32p_row04_traceSegment_051_0999_0013, g32p_row04_traceSegment_051_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 972 27 27, g32p_row04_traceSegment_051_0972_0027, g32p_row04_traceSegment_051_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1026 13 14, g32p_row04_traceSegment_051_1026_0013, g32p_row04_traceSegment_051_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1053 13 14, g32p_row04_traceSegment_051_1053_0013, g32p_row04_traceSegment_051_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1026 27 27, g32p_row04_traceSegment_051_1026_0027, g32p_row04_traceSegment_051_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 972 54 54, g32p_row04_traceSegment_051_0972_0054, g32p_row04_traceSegment_051_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 864 108 108, g32p_row04_traceSegment_051_0864_0108, g32p_row04_traceSegment_051_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1080 13 14, g32p_row04_traceSegment_051_1080_0013, g32p_row04_traceSegment_051_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1107 13 14, g32p_row04_traceSegment_051_1107_0013, g32p_row04_traceSegment_051_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1080 27 27, g32p_row04_traceSegment_051_1080_0027, g32p_row04_traceSegment_051_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1134 13 14, g32p_row04_traceSegment_051_1134_0013, g32p_row04_traceSegment_051_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1161 13 14, g32p_row04_traceSegment_051_1161_0013, g32p_row04_traceSegment_051_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1134 27 27, g32p_row04_traceSegment_051_1134_0027, g32p_row04_traceSegment_051_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1080 54 54, g32p_row04_traceSegment_051_1080_0054, g32p_row04_traceSegment_051_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1188 13 14, g32p_row04_traceSegment_051_1188_0013, g32p_row04_traceSegment_051_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1215 13 14, g32p_row04_traceSegment_051_1215_0013, g32p_row04_traceSegment_051_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1188 27 27, g32p_row04_traceSegment_051_1188_0027, g32p_row04_traceSegment_051_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1242 13 14, g32p_row04_traceSegment_051_1242_0013, g32p_row04_traceSegment_051_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1282 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1269 13 14, g32p_row04_traceSegment_051_1269_0013, g32p_row04_traceSegment_051_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1242 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1242 27 27, g32p_row04_traceSegment_051_1242_0027, g32p_row04_traceSegment_051_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1188 54 54, g32p_row04_traceSegment_051_1188_0054, g32p_row04_traceSegment_051_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1080 108 108, g32p_row04_traceSegment_051_1080_0108, g32p_row04_traceSegment_051_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_051 864 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 864 216 216, g32p_row04_traceSegment_051_0864_0216, g32p_row04_traceSegment_051_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1309 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1296 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1296 13 14, g32p_row04_traceSegment_051_1296_0013, g32p_row04_traceSegment_051_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1323 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1323 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1323 13 14, g32p_row04_traceSegment_051_1323_0013, g32p_row04_traceSegment_051_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1296 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1296 27 27, g32p_row04_traceSegment_051_1296_0027, g32p_row04_traceSegment_051_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1350 13 14, g32p_row04_traceSegment_051_1350_0013, g32p_row04_traceSegment_051_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1390 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1377 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1377 13 14, g32p_row04_traceSegment_051_1377_0013, g32p_row04_traceSegment_051_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1350 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1350 27 27, g32p_row04_traceSegment_051_1350_0027, g32p_row04_traceSegment_051_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 1296 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1296 54 54, g32p_row04_traceSegment_051_1296_0054, g32p_row04_traceSegment_051_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1404 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1417 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1404 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1404 13 14, g32p_row04_traceSegment_051_1404_0013, g32p_row04_traceSegment_051_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1431 13 14, g32p_row04_traceSegment_051_1431_0013, g32p_row04_traceSegment_051_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1404 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1404 27 27, g32p_row04_traceSegment_051_1404_0027, g32p_row04_traceSegment_051_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1458 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1458 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1458 13 14, g32p_row04_traceSegment_051_1458_0013, g32p_row04_traceSegment_051_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1485 13 14, g32p_row04_traceSegment_051_1485_0013, g32p_row04_traceSegment_051_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1458 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1458 27 27, g32p_row04_traceSegment_051_1458_0027, g32p_row04_traceSegment_051_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 1404 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1404 54 54, g32p_row04_traceSegment_051_1404_0054, g32p_row04_traceSegment_051_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 1296 216 = [0, 4, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1296 108 108, g32p_row04_traceSegment_051_1296_0108, g32p_row04_traceSegment_051_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1512 13 14, g32p_row04_traceSegment_051_1512_0013, g32p_row04_traceSegment_051_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1539 13 14, g32p_row04_traceSegment_051_1539_0013, g32p_row04_traceSegment_051_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1512 27 27, g32p_row04_traceSegment_051_1512_0027, g32p_row04_traceSegment_051_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1566 13 14, g32p_row04_traceSegment_051_1566_0013, g32p_row04_traceSegment_051_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1593 13 14, g32p_row04_traceSegment_051_1593_0013, g32p_row04_traceSegment_051_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1566 27 27, g32p_row04_traceSegment_051_1566_0027, g32p_row04_traceSegment_051_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1512 54 54, g32p_row04_traceSegment_051_1512_0054, g32p_row04_traceSegment_051_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1620 13 14, g32p_row04_traceSegment_051_1620_0013, g32p_row04_traceSegment_051_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1647 13 14, g32p_row04_traceSegment_051_1647_0013, g32p_row04_traceSegment_051_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1620 27 27, g32p_row04_traceSegment_051_1620_0027, g32p_row04_traceSegment_051_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1674 13 14, g32p_row04_traceSegment_051_1674_0013, g32p_row04_traceSegment_051_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_051 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_051 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_051_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_051 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1701 13 14, g32p_row04_traceSegment_051_1701_0013, g32p_row04_traceSegment_051_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_051 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1674 27 27, g32p_row04_traceSegment_051_1674_0027, g32p_row04_traceSegment_051_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_051 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1620 54 54, g32p_row04_traceSegment_051_1620_0054, g32p_row04_traceSegment_051_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_051 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1512 108 108, g32p_row04_traceSegment_051_1512_0108, g32p_row04_traceSegment_051_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_051_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_051 1296 432 = [0, 4, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 1296 216 216, g32p_row04_traceSegment_051_1296_0216, g32p_row04_traceSegment_051_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_051 864 864 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 864 432 432, g32p_row04_traceSegment_051_0864_0432, g32p_row04_traceSegment_051_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_051_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_051 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_051 0 864 864, g32p_row04_traceSegment_051_0000_0864, g32p_row04_traceSegment_051_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_051 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 51 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_051_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_052 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 52 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_052_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 0 13 14, g32p_row04_traceSegment_052_0000_0013, g32p_row04_traceSegment_052_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 27 13 14, g32p_row04_traceSegment_052_0027_0013, g32p_row04_traceSegment_052_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 0 27 27, g32p_row04_traceSegment_052_0000_0027, g32p_row04_traceSegment_052_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 54 13 14, g32p_row04_traceSegment_052_0054_0013, g32p_row04_traceSegment_052_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 81 13 14, g32p_row04_traceSegment_052_0081_0013, g32p_row04_traceSegment_052_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 54 27 27, g32p_row04_traceSegment_052_0054_0027, g32p_row04_traceSegment_052_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 0 54 54, g32p_row04_traceSegment_052_0000_0054, g32p_row04_traceSegment_052_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 108 13 14, g32p_row04_traceSegment_052_0108_0013, g32p_row04_traceSegment_052_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 135 13 14, g32p_row04_traceSegment_052_0135_0013, g32p_row04_traceSegment_052_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 108 27 27, g32p_row04_traceSegment_052_0108_0027, g32p_row04_traceSegment_052_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 162 13 14, g32p_row04_traceSegment_052_0162_0013, g32p_row04_traceSegment_052_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 189 13 14, g32p_row04_traceSegment_052_0189_0013, g32p_row04_traceSegment_052_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 162 27 27, g32p_row04_traceSegment_052_0162_0027, g32p_row04_traceSegment_052_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 108 54 54, g32p_row04_traceSegment_052_0108_0054, g32p_row04_traceSegment_052_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 0 108 108, g32p_row04_traceSegment_052_0000_0108, g32p_row04_traceSegment_052_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 216 13 14, g32p_row04_traceSegment_052_0216_0013, g32p_row04_traceSegment_052_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 243 13 14, g32p_row04_traceSegment_052_0243_0013, g32p_row04_traceSegment_052_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 216 27 27, g32p_row04_traceSegment_052_0216_0027, g32p_row04_traceSegment_052_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 270 13 14, g32p_row04_traceSegment_052_0270_0013, g32p_row04_traceSegment_052_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 297 13 14, g32p_row04_traceSegment_052_0297_0013, g32p_row04_traceSegment_052_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 270 27 27, g32p_row04_traceSegment_052_0270_0027, g32p_row04_traceSegment_052_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 216 54 54, g32p_row04_traceSegment_052_0216_0054, g32p_row04_traceSegment_052_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 324 13 14, g32p_row04_traceSegment_052_0324_0013, g32p_row04_traceSegment_052_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 351 13 14, g32p_row04_traceSegment_052_0351_0013, g32p_row04_traceSegment_052_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 324 27 27, g32p_row04_traceSegment_052_0324_0027, g32p_row04_traceSegment_052_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 378 13 14, g32p_row04_traceSegment_052_0378_0013, g32p_row04_traceSegment_052_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 405 13 14, g32p_row04_traceSegment_052_0405_0013, g32p_row04_traceSegment_052_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 378 27 27, g32p_row04_traceSegment_052_0378_0027, g32p_row04_traceSegment_052_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 324 54 54, g32p_row04_traceSegment_052_0324_0054, g32p_row04_traceSegment_052_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 216 108 108, g32p_row04_traceSegment_052_0216_0108, g32p_row04_traceSegment_052_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_052 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 0 216 216, g32p_row04_traceSegment_052_0000_0216, g32p_row04_traceSegment_052_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 432 13 14, g32p_row04_traceSegment_052_0432_0013, g32p_row04_traceSegment_052_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 459 13 14, g32p_row04_traceSegment_052_0459_0013, g32p_row04_traceSegment_052_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 432 27 27, g32p_row04_traceSegment_052_0432_0027, g32p_row04_traceSegment_052_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 486 13 14, g32p_row04_traceSegment_052_0486_0013, g32p_row04_traceSegment_052_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 513 13 14, g32p_row04_traceSegment_052_0513_0013, g32p_row04_traceSegment_052_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 486 27 27, g32p_row04_traceSegment_052_0486_0027, g32p_row04_traceSegment_052_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 432 54 54, g32p_row04_traceSegment_052_0432_0054, g32p_row04_traceSegment_052_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 540 13 14, g32p_row04_traceSegment_052_0540_0013, g32p_row04_traceSegment_052_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 567 13 14, g32p_row04_traceSegment_052_0567_0013, g32p_row04_traceSegment_052_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 540 27 27, g32p_row04_traceSegment_052_0540_0027, g32p_row04_traceSegment_052_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 594 13 14, g32p_row04_traceSegment_052_0594_0013, g32p_row04_traceSegment_052_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 621 13 14, g32p_row04_traceSegment_052_0621_0013, g32p_row04_traceSegment_052_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 594 27 27, g32p_row04_traceSegment_052_0594_0027, g32p_row04_traceSegment_052_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 540 54 54, g32p_row04_traceSegment_052_0540_0054, g32p_row04_traceSegment_052_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 432 108 108, g32p_row04_traceSegment_052_0432_0108, g32p_row04_traceSegment_052_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 648 13 14, g32p_row04_traceSegment_052_0648_0013, g32p_row04_traceSegment_052_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 675 13 14, g32p_row04_traceSegment_052_0675_0013, g32p_row04_traceSegment_052_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 648 27 27, g32p_row04_traceSegment_052_0648_0027, g32p_row04_traceSegment_052_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 702 13 14, g32p_row04_traceSegment_052_0702_0013, g32p_row04_traceSegment_052_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 729 13 14, g32p_row04_traceSegment_052_0729_0013, g32p_row04_traceSegment_052_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 702 27 27, g32p_row04_traceSegment_052_0702_0027, g32p_row04_traceSegment_052_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 648 54 54, g32p_row04_traceSegment_052_0648_0054, g32p_row04_traceSegment_052_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 756 13 14, g32p_row04_traceSegment_052_0756_0013, g32p_row04_traceSegment_052_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 783 13 14, g32p_row04_traceSegment_052_0783_0013, g32p_row04_traceSegment_052_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 756 27 27, g32p_row04_traceSegment_052_0756_0027, g32p_row04_traceSegment_052_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 810 13 14, g32p_row04_traceSegment_052_0810_0013, g32p_row04_traceSegment_052_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 837 13 14, g32p_row04_traceSegment_052_0837_0013, g32p_row04_traceSegment_052_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 810 27 27, g32p_row04_traceSegment_052_0810_0027, g32p_row04_traceSegment_052_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 756 54 54, g32p_row04_traceSegment_052_0756_0054, g32p_row04_traceSegment_052_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 648 108 108, g32p_row04_traceSegment_052_0648_0108, g32p_row04_traceSegment_052_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_052 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 432 216 216, g32p_row04_traceSegment_052_0432_0216, g32p_row04_traceSegment_052_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_052 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 0 432 432, g32p_row04_traceSegment_052_0000_0432, g32p_row04_traceSegment_052_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 864 13 14, g32p_row04_traceSegment_052_0864_0013, g32p_row04_traceSegment_052_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 891 13 14, g32p_row04_traceSegment_052_0891_0013, g32p_row04_traceSegment_052_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 864 27 27, g32p_row04_traceSegment_052_0864_0027, g32p_row04_traceSegment_052_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 918 13 14, g32p_row04_traceSegment_052_0918_0013, g32p_row04_traceSegment_052_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 945 13 14, g32p_row04_traceSegment_052_0945_0013, g32p_row04_traceSegment_052_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 918 27 27, g32p_row04_traceSegment_052_0918_0027, g32p_row04_traceSegment_052_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 864 54 54, g32p_row04_traceSegment_052_0864_0054, g32p_row04_traceSegment_052_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 972 13 14, g32p_row04_traceSegment_052_0972_0013, g32p_row04_traceSegment_052_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 999 13 14, g32p_row04_traceSegment_052_0999_0013, g32p_row04_traceSegment_052_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 972 27 27, g32p_row04_traceSegment_052_0972_0027, g32p_row04_traceSegment_052_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1026 13 14, g32p_row04_traceSegment_052_1026_0013, g32p_row04_traceSegment_052_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1053 13 14, g32p_row04_traceSegment_052_1053_0013, g32p_row04_traceSegment_052_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1026 27 27, g32p_row04_traceSegment_052_1026_0027, g32p_row04_traceSegment_052_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 972 54 54, g32p_row04_traceSegment_052_0972_0054, g32p_row04_traceSegment_052_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 864 108 108, g32p_row04_traceSegment_052_0864_0108, g32p_row04_traceSegment_052_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1080 13 14, g32p_row04_traceSegment_052_1080_0013, g32p_row04_traceSegment_052_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1107 13 14, g32p_row04_traceSegment_052_1107_0013, g32p_row04_traceSegment_052_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1080 27 27, g32p_row04_traceSegment_052_1080_0027, g32p_row04_traceSegment_052_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1134 13 14, g32p_row04_traceSegment_052_1134_0013, g32p_row04_traceSegment_052_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1161 13 14, g32p_row04_traceSegment_052_1161_0013, g32p_row04_traceSegment_052_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1134 27 27, g32p_row04_traceSegment_052_1134_0027, g32p_row04_traceSegment_052_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1080 54 54, g32p_row04_traceSegment_052_1080_0054, g32p_row04_traceSegment_052_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1188 13 14, g32p_row04_traceSegment_052_1188_0013, g32p_row04_traceSegment_052_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1215 13 14, g32p_row04_traceSegment_052_1215_0013, g32p_row04_traceSegment_052_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1188 27 27, g32p_row04_traceSegment_052_1188_0027, g32p_row04_traceSegment_052_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1242 13 14, g32p_row04_traceSegment_052_1242_0013, g32p_row04_traceSegment_052_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1269 13 14, g32p_row04_traceSegment_052_1269_0013, g32p_row04_traceSegment_052_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1242 27 27, g32p_row04_traceSegment_052_1242_0027, g32p_row04_traceSegment_052_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1188 54 54, g32p_row04_traceSegment_052_1188_0054, g32p_row04_traceSegment_052_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1080 108 108, g32p_row04_traceSegment_052_1080_0108, g32p_row04_traceSegment_052_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_052 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 864 216 216, g32p_row04_traceSegment_052_0864_0216, g32p_row04_traceSegment_052_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1296 13 14, g32p_row04_traceSegment_052_1296_0013, g32p_row04_traceSegment_052_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1323 13 14, g32p_row04_traceSegment_052_1323_0013, g32p_row04_traceSegment_052_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1296 27 27, g32p_row04_traceSegment_052_1296_0027, g32p_row04_traceSegment_052_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1350 13 14, g32p_row04_traceSegment_052_1350_0013, g32p_row04_traceSegment_052_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1377 13 14, g32p_row04_traceSegment_052_1377_0013, g32p_row04_traceSegment_052_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1350 27 27, g32p_row04_traceSegment_052_1350_0027, g32p_row04_traceSegment_052_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1296 54 54, g32p_row04_traceSegment_052_1296_0054, g32p_row04_traceSegment_052_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1404 13 14, g32p_row04_traceSegment_052_1404_0013, g32p_row04_traceSegment_052_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1431 13 14, g32p_row04_traceSegment_052_1431_0013, g32p_row04_traceSegment_052_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1404 27 27, g32p_row04_traceSegment_052_1404_0027, g32p_row04_traceSegment_052_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1458 13 14, g32p_row04_traceSegment_052_1458_0013, g32p_row04_traceSegment_052_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1485 13 14, g32p_row04_traceSegment_052_1485_0013, g32p_row04_traceSegment_052_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1458 27 27, g32p_row04_traceSegment_052_1458_0027, g32p_row04_traceSegment_052_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1404 54 54, g32p_row04_traceSegment_052_1404_0054, g32p_row04_traceSegment_052_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1296 108 108, g32p_row04_traceSegment_052_1296_0108, g32p_row04_traceSegment_052_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1512 13 14, g32p_row04_traceSegment_052_1512_0013, g32p_row04_traceSegment_052_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1539 13 14, g32p_row04_traceSegment_052_1539_0013, g32p_row04_traceSegment_052_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1512 27 27, g32p_row04_traceSegment_052_1512_0027, g32p_row04_traceSegment_052_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1579 14 = [0, 6] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1566 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1566 13 14, g32p_row04_traceSegment_052_1566_0013, g32p_row04_traceSegment_052_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1593 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1606 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1593 27 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1593 13 14, g32p_row04_traceSegment_052_1593_0013, g32p_row04_traceSegment_052_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1566 54 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1566 27 27, g32p_row04_traceSegment_052_1566_0027, g32p_row04_traceSegment_052_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 1512 108 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1512 54 54, g32p_row04_traceSegment_052_1512_0054, g32p_row04_traceSegment_052_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1620 13 14, g32p_row04_traceSegment_052_1620_0013, g32p_row04_traceSegment_052_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1647 13 14, g32p_row04_traceSegment_052_1647_0013, g32p_row04_traceSegment_052_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1620 27 27, g32p_row04_traceSegment_052_1620_0027, g32p_row04_traceSegment_052_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1674 13 14, g32p_row04_traceSegment_052_1674_0013, g32p_row04_traceSegment_052_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_052 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_052 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_052_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_052 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1701 13 14, g32p_row04_traceSegment_052_1701_0013, g32p_row04_traceSegment_052_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_052 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1674 27 27, g32p_row04_traceSegment_052_1674_0027, g32p_row04_traceSegment_052_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_052 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1620 54 54, g32p_row04_traceSegment_052_1620_0054, g32p_row04_traceSegment_052_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_052 1512 216 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1512 108 108, g32p_row04_traceSegment_052_1512_0108, g32p_row04_traceSegment_052_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_052_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_052 1296 432 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 1296 216 216, g32p_row04_traceSegment_052_1296_0216, g32p_row04_traceSegment_052_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_052 864 864 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 864 432 432, g32p_row04_traceSegment_052_0864_0432, g32p_row04_traceSegment_052_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_052_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_052 0 1728 = [0, 12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_052 0 864 864, g32p_row04_traceSegment_052_0000_0864, g32p_row04_traceSegment_052_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_052 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 52 = [0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_052_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_055 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 55 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_055_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 0 13 14, g32p_row04_traceSegment_055_0000_0013, g32p_row04_traceSegment_055_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 40 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 27 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 27 13 14, g32p_row04_traceSegment_055_0027_0013, g32p_row04_traceSegment_055_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 0 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 0 27 27, g32p_row04_traceSegment_055_0000_0027, g32p_row04_traceSegment_055_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 54 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 54 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 54 13 14, g32p_row04_traceSegment_055_0054_0013, g32p_row04_traceSegment_055_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 81 13 14, g32p_row04_traceSegment_055_0081_0013, g32p_row04_traceSegment_055_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 54 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 54 27 27, g32p_row04_traceSegment_055_0054_0027, g32p_row04_traceSegment_055_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 0 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 0 54 54, g32p_row04_traceSegment_055_0000_0054, g32p_row04_traceSegment_055_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 108 13 14, g32p_row04_traceSegment_055_0108_0013, g32p_row04_traceSegment_055_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 135 13 14, g32p_row04_traceSegment_055_0135_0013, g32p_row04_traceSegment_055_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 108 27 27, g32p_row04_traceSegment_055_0108_0027, g32p_row04_traceSegment_055_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 162 13 14, g32p_row04_traceSegment_055_0162_0013, g32p_row04_traceSegment_055_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 189 13 14, g32p_row04_traceSegment_055_0189_0013, g32p_row04_traceSegment_055_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 162 27 27, g32p_row04_traceSegment_055_0162_0027, g32p_row04_traceSegment_055_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 108 54 54, g32p_row04_traceSegment_055_0108_0054, g32p_row04_traceSegment_055_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 0 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 0 108 108, g32p_row04_traceSegment_055_0000_0108, g32p_row04_traceSegment_055_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 216 13 14, g32p_row04_traceSegment_055_0216_0013, g32p_row04_traceSegment_055_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 243 13 14, g32p_row04_traceSegment_055_0243_0013, g32p_row04_traceSegment_055_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 216 27 27, g32p_row04_traceSegment_055_0216_0027, g32p_row04_traceSegment_055_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 283 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 270 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 270 13 14, g32p_row04_traceSegment_055_0270_0013, g32p_row04_traceSegment_055_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 297 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 310 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 297 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 297 13 14, g32p_row04_traceSegment_055_0297_0013, g32p_row04_traceSegment_055_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 270 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 270 27 27, g32p_row04_traceSegment_055_0270_0027, g32p_row04_traceSegment_055_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 216 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 216 54 54, g32p_row04_traceSegment_055_0216_0054, g32p_row04_traceSegment_055_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 324 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 324 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 324 13 14, g32p_row04_traceSegment_055_0324_0013, g32p_row04_traceSegment_055_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 351 13 14, g32p_row04_traceSegment_055_0351_0013, g32p_row04_traceSegment_055_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 324 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 324 27 27, g32p_row04_traceSegment_055_0324_0027, g32p_row04_traceSegment_055_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 391 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 378 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 378 13 14, g32p_row04_traceSegment_055_0378_0013, g32p_row04_traceSegment_055_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 405 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 405 13 14, g32p_row04_traceSegment_055_0405_0013, g32p_row04_traceSegment_055_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 378 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 378 27 27, g32p_row04_traceSegment_055_0378_0027, g32p_row04_traceSegment_055_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 324 108 = [0, 2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 324 54 54, g32p_row04_traceSegment_055_0324_0054, g32p_row04_traceSegment_055_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 216 216 = [0, 6, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 216 108 108, g32p_row04_traceSegment_055_0216_0108, g32p_row04_traceSegment_055_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_055 0 432 = [0, 6, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 0 216 216, g32p_row04_traceSegment_055_0000_0216, g32p_row04_traceSegment_055_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 432 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 445 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 432 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 432 13 14, g32p_row04_traceSegment_055_0432_0013, g32p_row04_traceSegment_055_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 459 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 472 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 459 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 459 13 14, g32p_row04_traceSegment_055_0459_0013, g32p_row04_traceSegment_055_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 432 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 432 27 27, g32p_row04_traceSegment_055_0432_0027, g32p_row04_traceSegment_055_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 486 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 486 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 486 13 14, g32p_row04_traceSegment_055_0486_0013, g32p_row04_traceSegment_055_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 513 13 14, g32p_row04_traceSegment_055_0513_0013, g32p_row04_traceSegment_055_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 486 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 486 27 27, g32p_row04_traceSegment_055_0486_0027, g32p_row04_traceSegment_055_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 432 108 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 432 54 54, g32p_row04_traceSegment_055_0432_0054, g32p_row04_traceSegment_055_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 540 13 14, g32p_row04_traceSegment_055_0540_0013, g32p_row04_traceSegment_055_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 567 13 14, g32p_row04_traceSegment_055_0567_0013, g32p_row04_traceSegment_055_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 540 27 27, g32p_row04_traceSegment_055_0540_0027, g32p_row04_traceSegment_055_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 594 13 14, g32p_row04_traceSegment_055_0594_0013, g32p_row04_traceSegment_055_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 621 13 14, g32p_row04_traceSegment_055_0621_0013, g32p_row04_traceSegment_055_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 594 27 27, g32p_row04_traceSegment_055_0594_0027, g32p_row04_traceSegment_055_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 540 54 54, g32p_row04_traceSegment_055_0540_0054, g32p_row04_traceSegment_055_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 432 216 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 432 108 108, g32p_row04_traceSegment_055_0432_0108, g32p_row04_traceSegment_055_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 648 13 14, g32p_row04_traceSegment_055_0648_0013, g32p_row04_traceSegment_055_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 675 13 14, g32p_row04_traceSegment_055_0675_0013, g32p_row04_traceSegment_055_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 648 27 27, g32p_row04_traceSegment_055_0648_0027, g32p_row04_traceSegment_055_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 702 13 14, g32p_row04_traceSegment_055_0702_0013, g32p_row04_traceSegment_055_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 729 13 14, g32p_row04_traceSegment_055_0729_0013, g32p_row04_traceSegment_055_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 702 27 27, g32p_row04_traceSegment_055_0702_0027, g32p_row04_traceSegment_055_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 648 54 54, g32p_row04_traceSegment_055_0648_0054, g32p_row04_traceSegment_055_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 756 13 14, g32p_row04_traceSegment_055_0756_0013, g32p_row04_traceSegment_055_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 783 13 14, g32p_row04_traceSegment_055_0783_0013, g32p_row04_traceSegment_055_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 756 27 27, g32p_row04_traceSegment_055_0756_0027, g32p_row04_traceSegment_055_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 810 13 14, g32p_row04_traceSegment_055_0810_0013, g32p_row04_traceSegment_055_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 837 13 14, g32p_row04_traceSegment_055_0837_0013, g32p_row04_traceSegment_055_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 810 27 27, g32p_row04_traceSegment_055_0810_0027, g32p_row04_traceSegment_055_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 756 54 54, g32p_row04_traceSegment_055_0756_0054, g32p_row04_traceSegment_055_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 648 108 108, g32p_row04_traceSegment_055_0648_0108, g32p_row04_traceSegment_055_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_055 432 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 432 216 216, g32p_row04_traceSegment_055_0432_0216, g32p_row04_traceSegment_055_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_055 0 864 = [0, 6, 14] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 0 432 432, g32p_row04_traceSegment_055_0000_0432, g32p_row04_traceSegment_055_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 864 13 14, g32p_row04_traceSegment_055_0864_0013, g32p_row04_traceSegment_055_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 891 13 14, g32p_row04_traceSegment_055_0891_0013, g32p_row04_traceSegment_055_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 864 27 27, g32p_row04_traceSegment_055_0864_0027, g32p_row04_traceSegment_055_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 918 13 14, g32p_row04_traceSegment_055_0918_0013, g32p_row04_traceSegment_055_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 945 13 14, g32p_row04_traceSegment_055_0945_0013, g32p_row04_traceSegment_055_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 918 27 27, g32p_row04_traceSegment_055_0918_0027, g32p_row04_traceSegment_055_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 864 54 54, g32p_row04_traceSegment_055_0864_0054, g32p_row04_traceSegment_055_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 972 13 14, g32p_row04_traceSegment_055_0972_0013, g32p_row04_traceSegment_055_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 999 13 14, g32p_row04_traceSegment_055_0999_0013, g32p_row04_traceSegment_055_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 972 27 27, g32p_row04_traceSegment_055_0972_0027, g32p_row04_traceSegment_055_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1026 13 14, g32p_row04_traceSegment_055_1026_0013, g32p_row04_traceSegment_055_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1053 13 14, g32p_row04_traceSegment_055_1053_0013, g32p_row04_traceSegment_055_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1026 27 27, g32p_row04_traceSegment_055_1026_0027, g32p_row04_traceSegment_055_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 972 54 54, g32p_row04_traceSegment_055_0972_0054, g32p_row04_traceSegment_055_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 864 108 108, g32p_row04_traceSegment_055_0864_0108, g32p_row04_traceSegment_055_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1080 13 14, g32p_row04_traceSegment_055_1080_0013, g32p_row04_traceSegment_055_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1107 13 14, g32p_row04_traceSegment_055_1107_0013, g32p_row04_traceSegment_055_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1080 27 27, g32p_row04_traceSegment_055_1080_0027, g32p_row04_traceSegment_055_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1134 13 14, g32p_row04_traceSegment_055_1134_0013, g32p_row04_traceSegment_055_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1161 13 14, g32p_row04_traceSegment_055_1161_0013, g32p_row04_traceSegment_055_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1134 27 27, g32p_row04_traceSegment_055_1134_0027, g32p_row04_traceSegment_055_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1080 54 54, g32p_row04_traceSegment_055_1080_0054, g32p_row04_traceSegment_055_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1201 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1188 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1188 13 14, g32p_row04_traceSegment_055_1188_0013, g32p_row04_traceSegment_055_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1215 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1228 14 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1215 27 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1215 13 14, g32p_row04_traceSegment_055_1215_0013, g32p_row04_traceSegment_055_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1188 54 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1188 27 27, g32p_row04_traceSegment_055_1188_0027, g32p_row04_traceSegment_055_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1242 13 14, g32p_row04_traceSegment_055_1242_0013, g32p_row04_traceSegment_055_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1282 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1269 13 14, g32p_row04_traceSegment_055_1269_0013, g32p_row04_traceSegment_055_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1242 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1242 27 27, g32p_row04_traceSegment_055_1242_0027, g32p_row04_traceSegment_055_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 1188 108 = [0, 10, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1188 54 54, g32p_row04_traceSegment_055_1188_0054, g32p_row04_traceSegment_055_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 1080 216 = [0, 10, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1080 108 108, g32p_row04_traceSegment_055_1080_0108, g32p_row04_traceSegment_055_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_055 864 432 = [0, 10, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 864 216 216, g32p_row04_traceSegment_055_0864_0216, g32p_row04_traceSegment_055_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1296 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1296 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1296 13 14, g32p_row04_traceSegment_055_1296_0013, g32p_row04_traceSegment_055_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1323 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1336 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1323 27 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1323 13 14, g32p_row04_traceSegment_055_1323_0013, g32p_row04_traceSegment_055_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1296 54 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1296 27 27, g32p_row04_traceSegment_055_1296_0027, g32p_row04_traceSegment_055_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1350 13 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1363 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1350 27 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1350 13 14, g32p_row04_traceSegment_055_1350_0013, g32p_row04_traceSegment_055_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1377 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1390 14 = [0, 1, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1377 27 = [0, 3, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1377 13 14, g32p_row04_traceSegment_055_1377_0013, g32p_row04_traceSegment_055_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1350 54 = [0, 5, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1350 27 27, g32p_row04_traceSegment_055_1350_0027, g32p_row04_traceSegment_055_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 1296 108 = [0, 7, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1296 54 54, g32p_row04_traceSegment_055_1296_0054, g32p_row04_traceSegment_055_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1404 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1404 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1404 13 14, g32p_row04_traceSegment_055_1404_0013, g32p_row04_traceSegment_055_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1431 13 14, g32p_row04_traceSegment_055_1431_0013, g32p_row04_traceSegment_055_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1404 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1404 27 27, g32p_row04_traceSegment_055_1404_0027, g32p_row04_traceSegment_055_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1458 13 14, g32p_row04_traceSegment_055_1458_0013, g32p_row04_traceSegment_055_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1485 13 14, g32p_row04_traceSegment_055_1485_0013, g32p_row04_traceSegment_055_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1458 27 27, g32p_row04_traceSegment_055_1458_0027, g32p_row04_traceSegment_055_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 1404 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1404 54 54, g32p_row04_traceSegment_055_1404_0054, g32p_row04_traceSegment_055_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 1296 216 = [0, 8, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1296 108 108, g32p_row04_traceSegment_055_1296_0108, g32p_row04_traceSegment_055_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1512 13 14, g32p_row04_traceSegment_055_1512_0013, g32p_row04_traceSegment_055_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1539 13 14, g32p_row04_traceSegment_055_1539_0013, g32p_row04_traceSegment_055_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1512 27 27, g32p_row04_traceSegment_055_1512_0027, g32p_row04_traceSegment_055_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1566 13 14, g32p_row04_traceSegment_055_1566_0013, g32p_row04_traceSegment_055_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1593 13 14, g32p_row04_traceSegment_055_1593_0013, g32p_row04_traceSegment_055_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1566 27 27, g32p_row04_traceSegment_055_1566_0027, g32p_row04_traceSegment_055_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1512 54 54, g32p_row04_traceSegment_055_1512_0054, g32p_row04_traceSegment_055_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1620 13 14, g32p_row04_traceSegment_055_1620_0013, g32p_row04_traceSegment_055_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1647 13 14, g32p_row04_traceSegment_055_1647_0013, g32p_row04_traceSegment_055_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1620 27 27, g32p_row04_traceSegment_055_1620_0027, g32p_row04_traceSegment_055_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1674 13 14, g32p_row04_traceSegment_055_1674_0013, g32p_row04_traceSegment_055_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_055 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_055 1714 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_055_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_055 1701 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1701 13 14, g32p_row04_traceSegment_055_1701_0013, g32p_row04_traceSegment_055_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_055 1674 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1674 27 27, g32p_row04_traceSegment_055_1674_0027, g32p_row04_traceSegment_055_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_055 1620 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1620 54 54, g32p_row04_traceSegment_055_1620_0054, g32p_row04_traceSegment_055_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_055 1512 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1512 108 108, g32p_row04_traceSegment_055_1512_0108, g32p_row04_traceSegment_055_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_055_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_055 1296 432 = [0, 8, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 1296 216 216, g32p_row04_traceSegment_055_1296_0216, g32p_row04_traceSegment_055_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_055 864 864 = [0, 18, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 864 432 432, g32p_row04_traceSegment_055_0864_0432, g32p_row04_traceSegment_055_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_055_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_055 0 1728 = [0, 24, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_055 0 864 864, g32p_row04_traceSegment_055_0000_0864, g32p_row04_traceSegment_055_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_055 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 55 = [0, 24, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_055_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_056 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 56 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_056_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 13 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 0 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 0 13 14, g32p_row04_traceSegment_056_0000_0013, g32p_row04_traceSegment_056_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 27 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 27 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 27 13 14, g32p_row04_traceSegment_056_0027_0013, g32p_row04_traceSegment_056_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 0 54 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 0 27 27, g32p_row04_traceSegment_056_0000_0027, g32p_row04_traceSegment_056_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 54 13 14, g32p_row04_traceSegment_056_0054_0013, g32p_row04_traceSegment_056_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 81 13 14, g32p_row04_traceSegment_056_0081_0013, g32p_row04_traceSegment_056_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 54 27 27, g32p_row04_traceSegment_056_0054_0027, g32p_row04_traceSegment_056_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 0 108 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 0 54 54, g32p_row04_traceSegment_056_0000_0054, g32p_row04_traceSegment_056_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 108 13 14, g32p_row04_traceSegment_056_0108_0013, g32p_row04_traceSegment_056_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 135 13 14, g32p_row04_traceSegment_056_0135_0013, g32p_row04_traceSegment_056_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 108 27 27, g32p_row04_traceSegment_056_0108_0027, g32p_row04_traceSegment_056_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 162 13 14, g32p_row04_traceSegment_056_0162_0013, g32p_row04_traceSegment_056_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 189 13 14, g32p_row04_traceSegment_056_0189_0013, g32p_row04_traceSegment_056_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 162 27 27, g32p_row04_traceSegment_056_0162_0027, g32p_row04_traceSegment_056_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 108 54 54, g32p_row04_traceSegment_056_0108_0054, g32p_row04_traceSegment_056_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 0 216 = [2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 0 108 108, g32p_row04_traceSegment_056_0000_0108, g32p_row04_traceSegment_056_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 229 14 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 216 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 216 13 14, g32p_row04_traceSegment_056_0216_0013, g32p_row04_traceSegment_056_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 243 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 256 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 243 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 243 13 14, g32p_row04_traceSegment_056_0243_0013, g32p_row04_traceSegment_056_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 216 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 216 27 27, g32p_row04_traceSegment_056_0216_0027, g32p_row04_traceSegment_056_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 270 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 270 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 270 13 14, g32p_row04_traceSegment_056_0270_0013, g32p_row04_traceSegment_056_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 310 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 297 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 297 13 14, g32p_row04_traceSegment_056_0297_0013, g32p_row04_traceSegment_056_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 270 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 270 27 27, g32p_row04_traceSegment_056_0270_0027, g32p_row04_traceSegment_056_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 216 108 = [4, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 216 54 54, g32p_row04_traceSegment_056_0216_0054, g32p_row04_traceSegment_056_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 324 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 324 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 324 13 14, g32p_row04_traceSegment_056_0324_0013, g32p_row04_traceSegment_056_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 364 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 351 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 351 13 14, g32p_row04_traceSegment_056_0351_0013, g32p_row04_traceSegment_056_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 324 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 324 27 27, g32p_row04_traceSegment_056_0324_0027, g32p_row04_traceSegment_056_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 378 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 391 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 378 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 378 13 14, g32p_row04_traceSegment_056_0378_0013, g32p_row04_traceSegment_056_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 405 13 14, g32p_row04_traceSegment_056_0405_0013, g32p_row04_traceSegment_056_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 378 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 378 27 27, g32p_row04_traceSegment_056_0378_0027, g32p_row04_traceSegment_056_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 324 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 324 54 54, g32p_row04_traceSegment_056_0324_0054, g32p_row04_traceSegment_056_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 216 216 = [10, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 216 108 108, g32p_row04_traceSegment_056_0216_0108, g32p_row04_traceSegment_056_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_056 0 432 = [12, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 0 216 216, g32p_row04_traceSegment_056_0000_0216, g32p_row04_traceSegment_056_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 432 13 14, g32p_row04_traceSegment_056_0432_0013, g32p_row04_traceSegment_056_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 459 13 14, g32p_row04_traceSegment_056_0459_0013, g32p_row04_traceSegment_056_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 432 27 27, g32p_row04_traceSegment_056_0432_0027, g32p_row04_traceSegment_056_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 486 13 14, g32p_row04_traceSegment_056_0486_0013, g32p_row04_traceSegment_056_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 513 13 14, g32p_row04_traceSegment_056_0513_0013, g32p_row04_traceSegment_056_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 486 27 27, g32p_row04_traceSegment_056_0486_0027, g32p_row04_traceSegment_056_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 432 54 54, g32p_row04_traceSegment_056_0432_0054, g32p_row04_traceSegment_056_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 540 13 14, g32p_row04_traceSegment_056_0540_0013, g32p_row04_traceSegment_056_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 567 13 14, g32p_row04_traceSegment_056_0567_0013, g32p_row04_traceSegment_056_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 540 27 27, g32p_row04_traceSegment_056_0540_0027, g32p_row04_traceSegment_056_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 594 13 14, g32p_row04_traceSegment_056_0594_0013, g32p_row04_traceSegment_056_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 621 13 14, g32p_row04_traceSegment_056_0621_0013, g32p_row04_traceSegment_056_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 594 27 27, g32p_row04_traceSegment_056_0594_0027, g32p_row04_traceSegment_056_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 540 54 54, g32p_row04_traceSegment_056_0540_0054, g32p_row04_traceSegment_056_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 432 108 108, g32p_row04_traceSegment_056_0432_0108, g32p_row04_traceSegment_056_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 648 13 14, g32p_row04_traceSegment_056_0648_0013, g32p_row04_traceSegment_056_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 675 13 14, g32p_row04_traceSegment_056_0675_0013, g32p_row04_traceSegment_056_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 648 27 27, g32p_row04_traceSegment_056_0648_0027, g32p_row04_traceSegment_056_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 702 13 14, g32p_row04_traceSegment_056_0702_0013, g32p_row04_traceSegment_056_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 729 13 14, g32p_row04_traceSegment_056_0729_0013, g32p_row04_traceSegment_056_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 702 27 27, g32p_row04_traceSegment_056_0702_0027, g32p_row04_traceSegment_056_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 648 54 54, g32p_row04_traceSegment_056_0648_0054, g32p_row04_traceSegment_056_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 756 13 14, g32p_row04_traceSegment_056_0756_0013, g32p_row04_traceSegment_056_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 783 13 14, g32p_row04_traceSegment_056_0783_0013, g32p_row04_traceSegment_056_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 756 27 27, g32p_row04_traceSegment_056_0756_0027, g32p_row04_traceSegment_056_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 810 13 14, g32p_row04_traceSegment_056_0810_0013, g32p_row04_traceSegment_056_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 837 13 14, g32p_row04_traceSegment_056_0837_0013, g32p_row04_traceSegment_056_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 810 27 27, g32p_row04_traceSegment_056_0810_0027, g32p_row04_traceSegment_056_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 756 54 54, g32p_row04_traceSegment_056_0756_0054, g32p_row04_traceSegment_056_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 648 108 108, g32p_row04_traceSegment_056_0648_0108, g32p_row04_traceSegment_056_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_056 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 432 216 216, g32p_row04_traceSegment_056_0432_0216, g32p_row04_traceSegment_056_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_056 0 864 = [12, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 0 432 432, g32p_row04_traceSegment_056_0000_0432, g32p_row04_traceSegment_056_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 864 13 14, g32p_row04_traceSegment_056_0864_0013, g32p_row04_traceSegment_056_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 891 13 14, g32p_row04_traceSegment_056_0891_0013, g32p_row04_traceSegment_056_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 864 27 27, g32p_row04_traceSegment_056_0864_0027, g32p_row04_traceSegment_056_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 918 13 14, g32p_row04_traceSegment_056_0918_0013, g32p_row04_traceSegment_056_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 945 13 14, g32p_row04_traceSegment_056_0945_0013, g32p_row04_traceSegment_056_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 918 27 27, g32p_row04_traceSegment_056_0918_0027, g32p_row04_traceSegment_056_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 864 54 54, g32p_row04_traceSegment_056_0864_0054, g32p_row04_traceSegment_056_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 972 13 14, g32p_row04_traceSegment_056_0972_0013, g32p_row04_traceSegment_056_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 999 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 999 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 999 13 14, g32p_row04_traceSegment_056_0999_0013, g32p_row04_traceSegment_056_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 972 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 972 27 27, g32p_row04_traceSegment_056_0972_0027, g32p_row04_traceSegment_056_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1026 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1039 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1026 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1026 13 14, g32p_row04_traceSegment_056_1026_0013, g32p_row04_traceSegment_056_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1053 13 14, g32p_row04_traceSegment_056_1053_0013, g32p_row04_traceSegment_056_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1026 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1026 27 27, g32p_row04_traceSegment_056_1026_0027, g32p_row04_traceSegment_056_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 972 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 972 54 54, g32p_row04_traceSegment_056_0972_0054, g32p_row04_traceSegment_056_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 864 216 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 864 108 108, g32p_row04_traceSegment_056_0864_0108, g32p_row04_traceSegment_056_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1093 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1080 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1080 13 14, g32p_row04_traceSegment_056_1080_0013, g32p_row04_traceSegment_056_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1107 13 14, g32p_row04_traceSegment_056_1107_0013, g32p_row04_traceSegment_056_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1080 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1080 27 27, g32p_row04_traceSegment_056_1080_0027, g32p_row04_traceSegment_056_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1134 13 14, g32p_row04_traceSegment_056_1134_0013, g32p_row04_traceSegment_056_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1161 13 14, g32p_row04_traceSegment_056_1161_0013, g32p_row04_traceSegment_056_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1134 27 27, g32p_row04_traceSegment_056_1134_0027, g32p_row04_traceSegment_056_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 1080 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1080 54 54, g32p_row04_traceSegment_056_1080_0054, g32p_row04_traceSegment_056_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1188 13 14, g32p_row04_traceSegment_056_1188_0013, g32p_row04_traceSegment_056_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1215 13 14, g32p_row04_traceSegment_056_1215_0013, g32p_row04_traceSegment_056_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1188 27 27, g32p_row04_traceSegment_056_1188_0027, g32p_row04_traceSegment_056_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1255 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1242 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1242 13 14, g32p_row04_traceSegment_056_1242_0013, g32p_row04_traceSegment_056_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1269 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1269 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1269 13 14, g32p_row04_traceSegment_056_1269_0013, g32p_row04_traceSegment_056_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1242 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1242 27 27, g32p_row04_traceSegment_056_1242_0027, g32p_row04_traceSegment_056_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 1188 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1188 54 54, g32p_row04_traceSegment_056_1188_0054, g32p_row04_traceSegment_056_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 1080 216 = [2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1080 108 108, g32p_row04_traceSegment_056_1080_0108, g32p_row04_traceSegment_056_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_056 864 432 = [2, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 864 216 216, g32p_row04_traceSegment_056_0864_0216, g32p_row04_traceSegment_056_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1296 13 14, g32p_row04_traceSegment_056_1296_0013, g32p_row04_traceSegment_056_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1323 13 14, g32p_row04_traceSegment_056_1323_0013, g32p_row04_traceSegment_056_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1296 27 27, g32p_row04_traceSegment_056_1296_0027, g32p_row04_traceSegment_056_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1350 13 14, g32p_row04_traceSegment_056_1350_0013, g32p_row04_traceSegment_056_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1377 13 14, g32p_row04_traceSegment_056_1377_0013, g32p_row04_traceSegment_056_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1350 27 27, g32p_row04_traceSegment_056_1350_0027, g32p_row04_traceSegment_056_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1296 54 54, g32p_row04_traceSegment_056_1296_0054, g32p_row04_traceSegment_056_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1404 13 14, g32p_row04_traceSegment_056_1404_0013, g32p_row04_traceSegment_056_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1431 13 14, g32p_row04_traceSegment_056_1431_0013, g32p_row04_traceSegment_056_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1404 27 27, g32p_row04_traceSegment_056_1404_0027, g32p_row04_traceSegment_056_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1458 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1458 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1458 13 14, g32p_row04_traceSegment_056_1458_0013, g32p_row04_traceSegment_056_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1485 13 14, g32p_row04_traceSegment_056_1485_0013, g32p_row04_traceSegment_056_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1458 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1458 27 27, g32p_row04_traceSegment_056_1458_0027, g32p_row04_traceSegment_056_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 1404 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1404 54 54, g32p_row04_traceSegment_056_1404_0054, g32p_row04_traceSegment_056_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 1296 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1296 108 108, g32p_row04_traceSegment_056_1296_0108, g32p_row04_traceSegment_056_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1512 13 14, g32p_row04_traceSegment_056_1512_0013, g32p_row04_traceSegment_056_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1539 13 14, g32p_row04_traceSegment_056_1539_0013, g32p_row04_traceSegment_056_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1512 27 27, g32p_row04_traceSegment_056_1512_0027, g32p_row04_traceSegment_056_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1566 13 14, g32p_row04_traceSegment_056_1566_0013, g32p_row04_traceSegment_056_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1593 13 14, g32p_row04_traceSegment_056_1593_0013, g32p_row04_traceSegment_056_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1566 27 27, g32p_row04_traceSegment_056_1566_0027, g32p_row04_traceSegment_056_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1512 54 54, g32p_row04_traceSegment_056_1512_0054, g32p_row04_traceSegment_056_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1620 13 14, g32p_row04_traceSegment_056_1620_0013, g32p_row04_traceSegment_056_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1647 13 14, g32p_row04_traceSegment_056_1647_0013, g32p_row04_traceSegment_056_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1620 27 27, g32p_row04_traceSegment_056_1620_0027, g32p_row04_traceSegment_056_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1674 13 14, g32p_row04_traceSegment_056_1674_0013, g32p_row04_traceSegment_056_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_056 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_056 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_056_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_056 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1701 13 14, g32p_row04_traceSegment_056_1701_0013, g32p_row04_traceSegment_056_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_056 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1674 27 27, g32p_row04_traceSegment_056_1674_0027, g32p_row04_traceSegment_056_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_056 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1620 54 54, g32p_row04_traceSegment_056_1620_0054, g32p_row04_traceSegment_056_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_056 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1512 108 108, g32p_row04_traceSegment_056_1512_0108, g32p_row04_traceSegment_056_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_056_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_056 1296 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 1296 216 216, g32p_row04_traceSegment_056_1296_0216, g32p_row04_traceSegment_056_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_056 864 864 = [4, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 864 432 432, g32p_row04_traceSegment_056_0864_0432, g32p_row04_traceSegment_056_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_056_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_056 0 1728 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_056 0 864 864, g32p_row04_traceSegment_056_0000_0864, g32p_row04_traceSegment_056_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_056 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 56 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_056_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_058 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 58 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_058_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 0 13 14, g32p_row04_traceSegment_058_0000_0013, g32p_row04_traceSegment_058_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 27 13 14, g32p_row04_traceSegment_058_0027_0013, g32p_row04_traceSegment_058_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 0 27 27, g32p_row04_traceSegment_058_0000_0027, g32p_row04_traceSegment_058_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 54 13 14, g32p_row04_traceSegment_058_0054_0013, g32p_row04_traceSegment_058_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 81 13 14, g32p_row04_traceSegment_058_0081_0013, g32p_row04_traceSegment_058_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 54 27 27, g32p_row04_traceSegment_058_0054_0027, g32p_row04_traceSegment_058_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 0 54 54, g32p_row04_traceSegment_058_0000_0054, g32p_row04_traceSegment_058_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 108 13 14, g32p_row04_traceSegment_058_0108_0013, g32p_row04_traceSegment_058_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 148 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 135 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 135 13 14, g32p_row04_traceSegment_058_0135_0013, g32p_row04_traceSegment_058_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 108 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 108 27 27, g32p_row04_traceSegment_058_0108_0027, g32p_row04_traceSegment_058_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 162 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 175 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 162 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 162 13 14, g32p_row04_traceSegment_058_0162_0013, g32p_row04_traceSegment_058_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 189 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 189 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 189 13 14, g32p_row04_traceSegment_058_0189_0013, g32p_row04_traceSegment_058_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 162 54 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 162 27 27, g32p_row04_traceSegment_058_0162_0027, g32p_row04_traceSegment_058_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 108 108 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 108 54 54, g32p_row04_traceSegment_058_0108_0054, g32p_row04_traceSegment_058_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 0 216 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 0 108 108, g32p_row04_traceSegment_058_0000_0108, g32p_row04_traceSegment_058_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 216 13 14, g32p_row04_traceSegment_058_0216_0013, g32p_row04_traceSegment_058_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 243 13 14, g32p_row04_traceSegment_058_0243_0013, g32p_row04_traceSegment_058_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 216 27 27, g32p_row04_traceSegment_058_0216_0027, g32p_row04_traceSegment_058_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 270 13 14, g32p_row04_traceSegment_058_0270_0013, g32p_row04_traceSegment_058_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 297 13 14, g32p_row04_traceSegment_058_0297_0013, g32p_row04_traceSegment_058_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 270 27 27, g32p_row04_traceSegment_058_0270_0027, g32p_row04_traceSegment_058_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 216 54 54, g32p_row04_traceSegment_058_0216_0054, g32p_row04_traceSegment_058_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 324 13 14, g32p_row04_traceSegment_058_0324_0013, g32p_row04_traceSegment_058_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 351 13 14, g32p_row04_traceSegment_058_0351_0013, g32p_row04_traceSegment_058_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 324 27 27, g32p_row04_traceSegment_058_0324_0027, g32p_row04_traceSegment_058_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 378 13 14, g32p_row04_traceSegment_058_0378_0013, g32p_row04_traceSegment_058_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 405 13 14, g32p_row04_traceSegment_058_0405_0013, g32p_row04_traceSegment_058_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 378 27 27, g32p_row04_traceSegment_058_0378_0027, g32p_row04_traceSegment_058_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 324 54 54, g32p_row04_traceSegment_058_0324_0054, g32p_row04_traceSegment_058_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 216 108 108, g32p_row04_traceSegment_058_0216_0108, g32p_row04_traceSegment_058_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_058 0 432 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 0 216 216, g32p_row04_traceSegment_058_0000_0216, g32p_row04_traceSegment_058_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 432 13 14, g32p_row04_traceSegment_058_0432_0013, g32p_row04_traceSegment_058_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 459 13 14, g32p_row04_traceSegment_058_0459_0013, g32p_row04_traceSegment_058_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 432 27 27, g32p_row04_traceSegment_058_0432_0027, g32p_row04_traceSegment_058_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 486 13 14, g32p_row04_traceSegment_058_0486_0013, g32p_row04_traceSegment_058_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 513 13 14, g32p_row04_traceSegment_058_0513_0013, g32p_row04_traceSegment_058_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 486 27 27, g32p_row04_traceSegment_058_0486_0027, g32p_row04_traceSegment_058_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 432 54 54, g32p_row04_traceSegment_058_0432_0054, g32p_row04_traceSegment_058_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 540 13 14, g32p_row04_traceSegment_058_0540_0013, g32p_row04_traceSegment_058_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 567 13 14, g32p_row04_traceSegment_058_0567_0013, g32p_row04_traceSegment_058_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 540 27 27, g32p_row04_traceSegment_058_0540_0027, g32p_row04_traceSegment_058_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 594 13 14, g32p_row04_traceSegment_058_0594_0013, g32p_row04_traceSegment_058_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 621 13 14, g32p_row04_traceSegment_058_0621_0013, g32p_row04_traceSegment_058_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 594 27 27, g32p_row04_traceSegment_058_0594_0027, g32p_row04_traceSegment_058_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 540 54 54, g32p_row04_traceSegment_058_0540_0054, g32p_row04_traceSegment_058_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 432 108 108, g32p_row04_traceSegment_058_0432_0108, g32p_row04_traceSegment_058_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 648 13 14, g32p_row04_traceSegment_058_0648_0013, g32p_row04_traceSegment_058_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 675 13 14, g32p_row04_traceSegment_058_0675_0013, g32p_row04_traceSegment_058_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 648 27 27, g32p_row04_traceSegment_058_0648_0027, g32p_row04_traceSegment_058_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 702 13 14, g32p_row04_traceSegment_058_0702_0013, g32p_row04_traceSegment_058_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 729 13 14, g32p_row04_traceSegment_058_0729_0013, g32p_row04_traceSegment_058_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 702 27 27, g32p_row04_traceSegment_058_0702_0027, g32p_row04_traceSegment_058_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 648 54 54, g32p_row04_traceSegment_058_0648_0054, g32p_row04_traceSegment_058_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 756 13 14, g32p_row04_traceSegment_058_0756_0013, g32p_row04_traceSegment_058_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 783 13 14, g32p_row04_traceSegment_058_0783_0013, g32p_row04_traceSegment_058_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 756 27 27, g32p_row04_traceSegment_058_0756_0027, g32p_row04_traceSegment_058_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 810 13 14, g32p_row04_traceSegment_058_0810_0013, g32p_row04_traceSegment_058_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 837 13 = [5, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 850 14 = [1, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 837 27 = [6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 837 13 14, g32p_row04_traceSegment_058_0837_0013, g32p_row04_traceSegment_058_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 810 54 = [6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 810 27 27, g32p_row04_traceSegment_058_0810_0027, g32p_row04_traceSegment_058_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 756 108 = [6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 756 54 54, g32p_row04_traceSegment_058_0756_0054, g32p_row04_traceSegment_058_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 648 216 = [6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 648 108 108, g32p_row04_traceSegment_058_0648_0108, g32p_row04_traceSegment_058_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_058 432 432 = [6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 432 216 216, g32p_row04_traceSegment_058_0432_0216, g32p_row04_traceSegment_058_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_058 0 864 = [6, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 0 432 432, g32p_row04_traceSegment_058_0000_0432, g32p_row04_traceSegment_058_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 864 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 877 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 864 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 864 13 14, g32p_row04_traceSegment_058_0864_0013, g32p_row04_traceSegment_058_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 904 14 = [1, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 891 27 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 891 13 14, g32p_row04_traceSegment_058_0891_0013, g32p_row04_traceSegment_058_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 864 54 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 864 27 27, g32p_row04_traceSegment_058_0864_0027, g32p_row04_traceSegment_058_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 918 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 931 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 918 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 918 13 14, g32p_row04_traceSegment_058_0918_0013, g32p_row04_traceSegment_058_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 945 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 958 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 945 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 945 13 14, g32p_row04_traceSegment_058_0945_0013, g32p_row04_traceSegment_058_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 918 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 918 27 27, g32p_row04_traceSegment_058_0918_0027, g32p_row04_traceSegment_058_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 864 108 = [6, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 864 54 54, g32p_row04_traceSegment_058_0864_0054, g32p_row04_traceSegment_058_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 972 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 985 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 972 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 972 13 14, g32p_row04_traceSegment_058_0972_0013, g32p_row04_traceSegment_058_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 999 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1012 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 999 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 999 13 14, g32p_row04_traceSegment_058_0999_0013, g32p_row04_traceSegment_058_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 972 54 = [7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 972 27 27, g32p_row04_traceSegment_058_0972_0027, g32p_row04_traceSegment_058_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1026 13 14, g32p_row04_traceSegment_058_1026_0013, g32p_row04_traceSegment_058_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1053 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1066 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1053 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1053 13 14, g32p_row04_traceSegment_058_1053_0013, g32p_row04_traceSegment_058_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1026 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1026 27 27, g32p_row04_traceSegment_058_1026_0027, g32p_row04_traceSegment_058_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 972 108 = [7, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 972 54 54, g32p_row04_traceSegment_058_0972_0054, g32p_row04_traceSegment_058_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 864 216 = [13, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 864 108 108, g32p_row04_traceSegment_058_0864_0108, g32p_row04_traceSegment_058_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1080 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1080 13 14, g32p_row04_traceSegment_058_1080_0013, g32p_row04_traceSegment_058_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1107 13 14, g32p_row04_traceSegment_058_1107_0013, g32p_row04_traceSegment_058_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1080 54 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1080 27 27, g32p_row04_traceSegment_058_1080_0027, g32p_row04_traceSegment_058_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1134 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1147 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1134 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1134 13 14, g32p_row04_traceSegment_058_1134_0013, g32p_row04_traceSegment_058_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1161 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1161 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1161 13 14, g32p_row04_traceSegment_058_1161_0013, g32p_row04_traceSegment_058_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1134 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1134 27 27, g32p_row04_traceSegment_058_1134_0027, g32p_row04_traceSegment_058_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 1080 108 = [1, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1080 54 54, g32p_row04_traceSegment_058_1080_0054, g32p_row04_traceSegment_058_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1188 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1188 13 14, g32p_row04_traceSegment_058_1188_0013, g32p_row04_traceSegment_058_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1215 13 14, g32p_row04_traceSegment_058_1215_0013, g32p_row04_traceSegment_058_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1188 27 27, g32p_row04_traceSegment_058_1188_0027, g32p_row04_traceSegment_058_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1242 13 14, g32p_row04_traceSegment_058_1242_0013, g32p_row04_traceSegment_058_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1269 13 14, g32p_row04_traceSegment_058_1269_0013, g32p_row04_traceSegment_058_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1242 27 27, g32p_row04_traceSegment_058_1242_0027, g32p_row04_traceSegment_058_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1188 54 54, g32p_row04_traceSegment_058_1188_0054, g32p_row04_traceSegment_058_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 1080 216 = [1, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1080 108 108, g32p_row04_traceSegment_058_1080_0108, g32p_row04_traceSegment_058_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_058 864 432 = [14, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 864 216 216, g32p_row04_traceSegment_058_0864_0216, g32p_row04_traceSegment_058_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1296 13 14, g32p_row04_traceSegment_058_1296_0013, g32p_row04_traceSegment_058_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1323 13 14, g32p_row04_traceSegment_058_1323_0013, g32p_row04_traceSegment_058_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1296 27 27, g32p_row04_traceSegment_058_1296_0027, g32p_row04_traceSegment_058_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1350 13 14, g32p_row04_traceSegment_058_1350_0013, g32p_row04_traceSegment_058_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1377 13 14, g32p_row04_traceSegment_058_1377_0013, g32p_row04_traceSegment_058_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1350 27 27, g32p_row04_traceSegment_058_1350_0027, g32p_row04_traceSegment_058_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1296 54 54, g32p_row04_traceSegment_058_1296_0054, g32p_row04_traceSegment_058_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1404 13 14, g32p_row04_traceSegment_058_1404_0013, g32p_row04_traceSegment_058_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1431 13 14, g32p_row04_traceSegment_058_1431_0013, g32p_row04_traceSegment_058_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1404 27 27, g32p_row04_traceSegment_058_1404_0027, g32p_row04_traceSegment_058_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1458 13 14, g32p_row04_traceSegment_058_1458_0013, g32p_row04_traceSegment_058_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1485 13 14, g32p_row04_traceSegment_058_1485_0013, g32p_row04_traceSegment_058_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1458 27 27, g32p_row04_traceSegment_058_1458_0027, g32p_row04_traceSegment_058_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1404 54 54, g32p_row04_traceSegment_058_1404_0054, g32p_row04_traceSegment_058_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1296 108 108, g32p_row04_traceSegment_058_1296_0108, g32p_row04_traceSegment_058_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1512 13 14, g32p_row04_traceSegment_058_1512_0013, g32p_row04_traceSegment_058_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1539 13 14, g32p_row04_traceSegment_058_1539_0013, g32p_row04_traceSegment_058_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1512 27 27, g32p_row04_traceSegment_058_1512_0027, g32p_row04_traceSegment_058_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1566 13 14, g32p_row04_traceSegment_058_1566_0013, g32p_row04_traceSegment_058_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1593 13 14, g32p_row04_traceSegment_058_1593_0013, g32p_row04_traceSegment_058_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1566 27 27, g32p_row04_traceSegment_058_1566_0027, g32p_row04_traceSegment_058_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1512 54 54, g32p_row04_traceSegment_058_1512_0054, g32p_row04_traceSegment_058_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1620 13 14, g32p_row04_traceSegment_058_1620_0013, g32p_row04_traceSegment_058_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1647 13 14, g32p_row04_traceSegment_058_1647_0013, g32p_row04_traceSegment_058_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1620 27 27, g32p_row04_traceSegment_058_1620_0027, g32p_row04_traceSegment_058_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1674 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1687 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1674 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1674 13 14, g32p_row04_traceSegment_058_1674_0013, g32p_row04_traceSegment_058_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_058 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_058 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_058_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_058 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1701 13 14, g32p_row04_traceSegment_058_1701_0013, g32p_row04_traceSegment_058_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_058 1674 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1674 27 27, g32p_row04_traceSegment_058_1674_0027, g32p_row04_traceSegment_058_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_058 1620 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1620 54 54, g32p_row04_traceSegment_058_1620_0054, g32p_row04_traceSegment_058_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_058 1512 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1512 108 108, g32p_row04_traceSegment_058_1512_0108, g32p_row04_traceSegment_058_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_058_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_058 1296 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 1296 216 216, g32p_row04_traceSegment_058_1296_0216, g32p_row04_traceSegment_058_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_058 864 864 = [18, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 864 432 432, g32p_row04_traceSegment_058_0864_0432, g32p_row04_traceSegment_058_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_058_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_058 0 1728 = [24, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_058 0 864 864, g32p_row04_traceSegment_058_0000_0864, g32p_row04_traceSegment_058_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_058 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 58 = [24, 0, 24] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_058_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_045 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 45) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 45) (g32p_literalTraceValue 3 45)
      [1, 1, 1] [5184] = true := by
  rw [g32p_row04_traceCoefficients_045]
  decide +kernel

theorem g32p_row04_tracePolynomial_048 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 48) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 48) (g32p_literalTraceValue 3 48)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_048]
  decide +kernel

theorem g32p_row04_tracePolynomial_050 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 50) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 50) (g32p_literalTraceValue 3 50)
      [1, 1, 1] [3456] = true := by
  rw [g32p_row04_traceCoefficients_050]
  decide +kernel

theorem g32p_row04_tracePolynomial_051 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 51) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 51) (g32p_literalTraceValue 3 51)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_051]
  decide +kernel

theorem g32p_row04_tracePolynomial_052 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 52) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 52) (g32p_literalTraceValue 3 52)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_052]
  decide +kernel

theorem g32p_row04_tracePolynomial_055 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 55) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 55) (g32p_literalTraceValue 3 55)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_055]
  decide +kernel

theorem g32p_row04_tracePolynomial_056 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 56) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 56) (g32p_literalTraceValue 3 56)
      [1, 1, 1] [10368] = true := by
  rw [g32p_row04_traceCoefficients_056]
  decide +kernel

theorem g32p_row04_tracePolynomial_058 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 58) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 58) (g32p_literalTraceValue 3 58)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_058]
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

private def g32p_row04_traceSegment_059 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 59 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_059_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 0 13 14, g32p_row04_traceSegment_059_0000_0013, g32p_row04_traceSegment_059_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 27 13 14, g32p_row04_traceSegment_059_0027_0013, g32p_row04_traceSegment_059_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 0 27 27, g32p_row04_traceSegment_059_0000_0027, g32p_row04_traceSegment_059_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 54 13 14, g32p_row04_traceSegment_059_0054_0013, g32p_row04_traceSegment_059_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 81 13 14, g32p_row04_traceSegment_059_0081_0013, g32p_row04_traceSegment_059_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 54 27 27, g32p_row04_traceSegment_059_0054_0027, g32p_row04_traceSegment_059_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 0 54 54, g32p_row04_traceSegment_059_0000_0054, g32p_row04_traceSegment_059_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 108 13 14, g32p_row04_traceSegment_059_0108_0013, g32p_row04_traceSegment_059_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 135 13 14, g32p_row04_traceSegment_059_0135_0013, g32p_row04_traceSegment_059_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 108 27 27, g32p_row04_traceSegment_059_0108_0027, g32p_row04_traceSegment_059_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 162 13 14, g32p_row04_traceSegment_059_0162_0013, g32p_row04_traceSegment_059_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 189 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 202 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 189 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 189 13 14, g32p_row04_traceSegment_059_0189_0013, g32p_row04_traceSegment_059_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 162 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 162 27 27, g32p_row04_traceSegment_059_0162_0027, g32p_row04_traceSegment_059_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 108 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 108 54 54, g32p_row04_traceSegment_059_0108_0054, g32p_row04_traceSegment_059_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 0 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 0 108 108, g32p_row04_traceSegment_059_0000_0108, g32p_row04_traceSegment_059_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 216 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 229 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 216 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 216 13 14, g32p_row04_traceSegment_059_0216_0013, g32p_row04_traceSegment_059_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 243 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 256 14 = [0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 243 27 = [0, 7] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 243 13 14, g32p_row04_traceSegment_059_0243_0013, g32p_row04_traceSegment_059_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 216 54 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 216 27 27, g32p_row04_traceSegment_059_0216_0027, g32p_row04_traceSegment_059_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 270 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 270 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 270 13 14, g32p_row04_traceSegment_059_0270_0013, g32p_row04_traceSegment_059_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 297 13 14, g32p_row04_traceSegment_059_0297_0013, g32p_row04_traceSegment_059_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 270 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 270 27 27, g32p_row04_traceSegment_059_0270_0027, g32p_row04_traceSegment_059_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 216 108 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 216 54 54, g32p_row04_traceSegment_059_0216_0054, g32p_row04_traceSegment_059_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 324 13 14, g32p_row04_traceSegment_059_0324_0013, g32p_row04_traceSegment_059_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 351 13 14, g32p_row04_traceSegment_059_0351_0013, g32p_row04_traceSegment_059_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 324 27 27, g32p_row04_traceSegment_059_0324_0027, g32p_row04_traceSegment_059_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 378 13 14, g32p_row04_traceSegment_059_0378_0013, g32p_row04_traceSegment_059_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 405 13 14, g32p_row04_traceSegment_059_0405_0013, g32p_row04_traceSegment_059_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 378 27 27, g32p_row04_traceSegment_059_0378_0027, g32p_row04_traceSegment_059_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 324 54 54, g32p_row04_traceSegment_059_0324_0054, g32p_row04_traceSegment_059_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 216 216 = [0, 11] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 216 108 108, g32p_row04_traceSegment_059_0216_0108, g32p_row04_traceSegment_059_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_059 0 432 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 0 216 216, g32p_row04_traceSegment_059_0000_0216, g32p_row04_traceSegment_059_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 432 13 14, g32p_row04_traceSegment_059_0432_0013, g32p_row04_traceSegment_059_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 459 13 14, g32p_row04_traceSegment_059_0459_0013, g32p_row04_traceSegment_059_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 432 27 27, g32p_row04_traceSegment_059_0432_0027, g32p_row04_traceSegment_059_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 486 13 14, g32p_row04_traceSegment_059_0486_0013, g32p_row04_traceSegment_059_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 513 13 14, g32p_row04_traceSegment_059_0513_0013, g32p_row04_traceSegment_059_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 486 27 27, g32p_row04_traceSegment_059_0486_0027, g32p_row04_traceSegment_059_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 432 54 54, g32p_row04_traceSegment_059_0432_0054, g32p_row04_traceSegment_059_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 540 13 14, g32p_row04_traceSegment_059_0540_0013, g32p_row04_traceSegment_059_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 567 13 14, g32p_row04_traceSegment_059_0567_0013, g32p_row04_traceSegment_059_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 540 27 27, g32p_row04_traceSegment_059_0540_0027, g32p_row04_traceSegment_059_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 594 13 14, g32p_row04_traceSegment_059_0594_0013, g32p_row04_traceSegment_059_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 621 13 14, g32p_row04_traceSegment_059_0621_0013, g32p_row04_traceSegment_059_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 594 27 27, g32p_row04_traceSegment_059_0594_0027, g32p_row04_traceSegment_059_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 540 54 54, g32p_row04_traceSegment_059_0540_0054, g32p_row04_traceSegment_059_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 432 108 108, g32p_row04_traceSegment_059_0432_0108, g32p_row04_traceSegment_059_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 648 13 14, g32p_row04_traceSegment_059_0648_0013, g32p_row04_traceSegment_059_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 675 13 14, g32p_row04_traceSegment_059_0675_0013, g32p_row04_traceSegment_059_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 648 27 27, g32p_row04_traceSegment_059_0648_0027, g32p_row04_traceSegment_059_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 702 13 14, g32p_row04_traceSegment_059_0702_0013, g32p_row04_traceSegment_059_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 729 13 14, g32p_row04_traceSegment_059_0729_0013, g32p_row04_traceSegment_059_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 702 27 27, g32p_row04_traceSegment_059_0702_0027, g32p_row04_traceSegment_059_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 648 54 54, g32p_row04_traceSegment_059_0648_0054, g32p_row04_traceSegment_059_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 756 13 14, g32p_row04_traceSegment_059_0756_0013, g32p_row04_traceSegment_059_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 783 13 14, g32p_row04_traceSegment_059_0783_0013, g32p_row04_traceSegment_059_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 756 27 27, g32p_row04_traceSegment_059_0756_0027, g32p_row04_traceSegment_059_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 810 13 14, g32p_row04_traceSegment_059_0810_0013, g32p_row04_traceSegment_059_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 837 13 14, g32p_row04_traceSegment_059_0837_0013, g32p_row04_traceSegment_059_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 810 27 27, g32p_row04_traceSegment_059_0810_0027, g32p_row04_traceSegment_059_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 756 54 54, g32p_row04_traceSegment_059_0756_0054, g32p_row04_traceSegment_059_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 648 108 108, g32p_row04_traceSegment_059_0648_0108, g32p_row04_traceSegment_059_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_059 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 432 216 216, g32p_row04_traceSegment_059_0432_0216, g32p_row04_traceSegment_059_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_059 0 864 = [0, 15] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 0 432 432, g32p_row04_traceSegment_059_0000_0432, g32p_row04_traceSegment_059_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 864 13 14, g32p_row04_traceSegment_059_0864_0013, g32p_row04_traceSegment_059_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 891 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 904 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 891 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 891 13 14, g32p_row04_traceSegment_059_0891_0013, g32p_row04_traceSegment_059_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 864 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 864 27 27, g32p_row04_traceSegment_059_0864_0027, g32p_row04_traceSegment_059_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 918 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 918 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 918 13 14, g32p_row04_traceSegment_059_0918_0013, g32p_row04_traceSegment_059_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 945 13 14, g32p_row04_traceSegment_059_0945_0013, g32p_row04_traceSegment_059_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 918 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 918 27 27, g32p_row04_traceSegment_059_0918_0027, g32p_row04_traceSegment_059_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 864 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 864 54 54, g32p_row04_traceSegment_059_0864_0054, g32p_row04_traceSegment_059_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 985 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 972 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 972 13 14, g32p_row04_traceSegment_059_0972_0013, g32p_row04_traceSegment_059_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 999 13 14, g32p_row04_traceSegment_059_0999_0013, g32p_row04_traceSegment_059_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 972 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 972 27 27, g32p_row04_traceSegment_059_0972_0027, g32p_row04_traceSegment_059_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1026 13 14, g32p_row04_traceSegment_059_1026_0013, g32p_row04_traceSegment_059_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1053 13 14, g32p_row04_traceSegment_059_1053_0013, g32p_row04_traceSegment_059_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1026 27 27, g32p_row04_traceSegment_059_1026_0027, g32p_row04_traceSegment_059_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 972 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 972 54 54, g32p_row04_traceSegment_059_0972_0054, g32p_row04_traceSegment_059_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 864 216 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 864 108 108, g32p_row04_traceSegment_059_0864_0108, g32p_row04_traceSegment_059_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1080 13 14, g32p_row04_traceSegment_059_1080_0013, g32p_row04_traceSegment_059_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1107 13 14, g32p_row04_traceSegment_059_1107_0013, g32p_row04_traceSegment_059_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1080 27 27, g32p_row04_traceSegment_059_1080_0027, g32p_row04_traceSegment_059_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1134 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1134 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1134 13 14, g32p_row04_traceSegment_059_1134_0013, g32p_row04_traceSegment_059_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1161 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1161 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1161 13 14, g32p_row04_traceSegment_059_1161_0013, g32p_row04_traceSegment_059_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1134 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1134 27 27, g32p_row04_traceSegment_059_1134_0027, g32p_row04_traceSegment_059_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 1080 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1080 54 54, g32p_row04_traceSegment_059_1080_0054, g32p_row04_traceSegment_059_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1188 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1201 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1188 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1188 13 14, g32p_row04_traceSegment_059_1188_0013, g32p_row04_traceSegment_059_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1215 13 14, g32p_row04_traceSegment_059_1215_0013, g32p_row04_traceSegment_059_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1188 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1188 27 27, g32p_row04_traceSegment_059_1188_0027, g32p_row04_traceSegment_059_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1242 13 14, g32p_row04_traceSegment_059_1242_0013, g32p_row04_traceSegment_059_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1269 13 14, g32p_row04_traceSegment_059_1269_0013, g32p_row04_traceSegment_059_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1242 27 27, g32p_row04_traceSegment_059_1242_0027, g32p_row04_traceSegment_059_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 1188 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1188 54 54, g32p_row04_traceSegment_059_1188_0054, g32p_row04_traceSegment_059_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 1080 216 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1080 108 108, g32p_row04_traceSegment_059_1080_0108, g32p_row04_traceSegment_059_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_059 864 432 = [0, 9] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 864 216 216, g32p_row04_traceSegment_059_0864_0216, g32p_row04_traceSegment_059_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1296 13 14, g32p_row04_traceSegment_059_1296_0013, g32p_row04_traceSegment_059_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1323 13 14, g32p_row04_traceSegment_059_1323_0013, g32p_row04_traceSegment_059_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1296 27 27, g32p_row04_traceSegment_059_1296_0027, g32p_row04_traceSegment_059_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1350 13 14, g32p_row04_traceSegment_059_1350_0013, g32p_row04_traceSegment_059_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1377 13 14, g32p_row04_traceSegment_059_1377_0013, g32p_row04_traceSegment_059_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1350 27 27, g32p_row04_traceSegment_059_1350_0027, g32p_row04_traceSegment_059_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1296 54 54, g32p_row04_traceSegment_059_1296_0054, g32p_row04_traceSegment_059_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1404 13 14, g32p_row04_traceSegment_059_1404_0013, g32p_row04_traceSegment_059_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1431 13 14, g32p_row04_traceSegment_059_1431_0013, g32p_row04_traceSegment_059_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1404 27 27, g32p_row04_traceSegment_059_1404_0027, g32p_row04_traceSegment_059_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1458 13 14, g32p_row04_traceSegment_059_1458_0013, g32p_row04_traceSegment_059_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1485 13 14, g32p_row04_traceSegment_059_1485_0013, g32p_row04_traceSegment_059_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1458 27 27, g32p_row04_traceSegment_059_1458_0027, g32p_row04_traceSegment_059_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1404 54 54, g32p_row04_traceSegment_059_1404_0054, g32p_row04_traceSegment_059_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1296 108 108, g32p_row04_traceSegment_059_1296_0108, g32p_row04_traceSegment_059_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1512 13 14, g32p_row04_traceSegment_059_1512_0013, g32p_row04_traceSegment_059_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1539 13 14, g32p_row04_traceSegment_059_1539_0013, g32p_row04_traceSegment_059_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1512 27 27, g32p_row04_traceSegment_059_1512_0027, g32p_row04_traceSegment_059_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1566 13 14, g32p_row04_traceSegment_059_1566_0013, g32p_row04_traceSegment_059_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1593 13 14, g32p_row04_traceSegment_059_1593_0013, g32p_row04_traceSegment_059_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1566 27 27, g32p_row04_traceSegment_059_1566_0027, g32p_row04_traceSegment_059_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1512 54 54, g32p_row04_traceSegment_059_1512_0054, g32p_row04_traceSegment_059_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1620 13 14, g32p_row04_traceSegment_059_1620_0013, g32p_row04_traceSegment_059_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1647 13 14, g32p_row04_traceSegment_059_1647_0013, g32p_row04_traceSegment_059_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1620 27 27, g32p_row04_traceSegment_059_1620_0027, g32p_row04_traceSegment_059_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1674 13 = [0, 5] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1674 27 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1674 13 14, g32p_row04_traceSegment_059_1674_0013, g32p_row04_traceSegment_059_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_059 1701 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_059 1714 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_059_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_059 1701 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1701 13 14, g32p_row04_traceSegment_059_1701_0013, g32p_row04_traceSegment_059_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_059 1674 54 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1674 27 27, g32p_row04_traceSegment_059_1674_0027, g32p_row04_traceSegment_059_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_059 1620 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1620 54 54, g32p_row04_traceSegment_059_1620_0054, g32p_row04_traceSegment_059_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_059 1512 216 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1512 108 108, g32p_row04_traceSegment_059_1512_0108, g32p_row04_traceSegment_059_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_059_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_059 1296 432 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 1296 216 216, g32p_row04_traceSegment_059_1296_0216, g32p_row04_traceSegment_059_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_059 864 864 = [0, 17] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 864 432 432, g32p_row04_traceSegment_059_0864_0432, g32p_row04_traceSegment_059_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_059_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_059 0 1728 = [0, 32] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_059 0 864 864, g32p_row04_traceSegment_059_0000_0864, g32p_row04_traceSegment_059_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_059 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 59 = [0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_059_0000_1728

end HodgeLean.Foundations.Program

end
end
