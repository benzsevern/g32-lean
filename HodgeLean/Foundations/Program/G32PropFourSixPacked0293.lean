import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0292

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_004 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 4 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_004_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 13 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 0 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 13 14, g32p_row02_traceSegment_004_0000_0013, g32p_row02_traceSegment_004_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 40 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 27 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 27 13 14, g32p_row02_traceSegment_004_0027_0013, g32p_row02_traceSegment_004_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 0 54 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 27 27, g32p_row02_traceSegment_004_0000_0027, g32p_row02_traceSegment_004_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 54 13 14, g32p_row02_traceSegment_004_0054_0013, g32p_row02_traceSegment_004_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 94 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 81 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 81 13 14, g32p_row02_traceSegment_004_0081_0013, g32p_row02_traceSegment_004_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 54 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 54 27 27, g32p_row02_traceSegment_004_0054_0027, g32p_row02_traceSegment_004_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 0 108 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 54 54, g32p_row02_traceSegment_004_0000_0054, g32p_row02_traceSegment_004_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 108 13 14, g32p_row02_traceSegment_004_0108_0013, g32p_row02_traceSegment_004_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 135 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 135 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 135 13 14, g32p_row02_traceSegment_004_0135_0013, g32p_row02_traceSegment_004_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 108 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 108 27 27, g32p_row02_traceSegment_004_0108_0027, g32p_row02_traceSegment_004_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 162 13 14, g32p_row02_traceSegment_004_0162_0013, g32p_row02_traceSegment_004_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 189 13 14, g32p_row02_traceSegment_004_0189_0013, g32p_row02_traceSegment_004_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 162 27 27, g32p_row02_traceSegment_004_0162_0027, g32p_row02_traceSegment_004_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 108 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 108 54 54, g32p_row02_traceSegment_004_0108_0054, g32p_row02_traceSegment_004_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 0 216 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 108 108, g32p_row02_traceSegment_004_0000_0108, g32p_row02_traceSegment_004_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 216 13 14, g32p_row02_traceSegment_004_0216_0013, g32p_row02_traceSegment_004_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 243 13 14, g32p_row02_traceSegment_004_0243_0013, g32p_row02_traceSegment_004_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 216 27 27, g32p_row02_traceSegment_004_0216_0027, g32p_row02_traceSegment_004_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 270 13 14, g32p_row02_traceSegment_004_0270_0013, g32p_row02_traceSegment_004_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 297 13 14, g32p_row02_traceSegment_004_0297_0013, g32p_row02_traceSegment_004_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 270 27 27, g32p_row02_traceSegment_004_0270_0027, g32p_row02_traceSegment_004_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 216 54 54, g32p_row02_traceSegment_004_0216_0054, g32p_row02_traceSegment_004_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 324 13 14, g32p_row02_traceSegment_004_0324_0013, g32p_row02_traceSegment_004_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 351 13 14, g32p_row02_traceSegment_004_0351_0013, g32p_row02_traceSegment_004_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 324 27 27, g32p_row02_traceSegment_004_0324_0027, g32p_row02_traceSegment_004_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 378 13 14, g32p_row02_traceSegment_004_0378_0013, g32p_row02_traceSegment_004_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 405 13 14, g32p_row02_traceSegment_004_0405_0013, g32p_row02_traceSegment_004_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 378 27 27, g32p_row02_traceSegment_004_0378_0027, g32p_row02_traceSegment_004_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 324 54 54, g32p_row02_traceSegment_004_0324_0054, g32p_row02_traceSegment_004_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 216 108 108, g32p_row02_traceSegment_004_0216_0108, g32p_row02_traceSegment_004_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 0 432 = [1, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 216 216, g32p_row02_traceSegment_004_0000_0216, g32p_row02_traceSegment_004_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 432 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 432 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 432 13 14, g32p_row02_traceSegment_004_0432_0013, g32p_row02_traceSegment_004_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 459 13 14, g32p_row02_traceSegment_004_0459_0013, g32p_row02_traceSegment_004_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 432 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 432 27 27, g32p_row02_traceSegment_004_0432_0027, g32p_row02_traceSegment_004_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 486 13 14, g32p_row02_traceSegment_004_0486_0013, g32p_row02_traceSegment_004_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 513 13 14, g32p_row02_traceSegment_004_0513_0013, g32p_row02_traceSegment_004_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 486 27 27, g32p_row02_traceSegment_004_0486_0027, g32p_row02_traceSegment_004_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 432 54 54, g32p_row02_traceSegment_004_0432_0054, g32p_row02_traceSegment_004_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 540 13 14, g32p_row02_traceSegment_004_0540_0013, g32p_row02_traceSegment_004_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 567 13 14, g32p_row02_traceSegment_004_0567_0013, g32p_row02_traceSegment_004_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 540 27 27, g32p_row02_traceSegment_004_0540_0027, g32p_row02_traceSegment_004_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 594 13 14, g32p_row02_traceSegment_004_0594_0013, g32p_row02_traceSegment_004_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 621 13 14, g32p_row02_traceSegment_004_0621_0013, g32p_row02_traceSegment_004_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 594 27 27, g32p_row02_traceSegment_004_0594_0027, g32p_row02_traceSegment_004_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 540 54 54, g32p_row02_traceSegment_004_0540_0054, g32p_row02_traceSegment_004_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 432 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 432 108 108, g32p_row02_traceSegment_004_0432_0108, g32p_row02_traceSegment_004_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 648 13 14, g32p_row02_traceSegment_004_0648_0013, g32p_row02_traceSegment_004_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 675 13 14, g32p_row02_traceSegment_004_0675_0013, g32p_row02_traceSegment_004_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 648 27 27, g32p_row02_traceSegment_004_0648_0027, g32p_row02_traceSegment_004_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 702 13 14, g32p_row02_traceSegment_004_0702_0013, g32p_row02_traceSegment_004_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 729 13 14, g32p_row02_traceSegment_004_0729_0013, g32p_row02_traceSegment_004_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 702 27 27, g32p_row02_traceSegment_004_0702_0027, g32p_row02_traceSegment_004_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 648 54 54, g32p_row02_traceSegment_004_0648_0054, g32p_row02_traceSegment_004_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 756 13 14, g32p_row02_traceSegment_004_0756_0013, g32p_row02_traceSegment_004_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 783 13 14, g32p_row02_traceSegment_004_0783_0013, g32p_row02_traceSegment_004_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 756 27 27, g32p_row02_traceSegment_004_0756_0027, g32p_row02_traceSegment_004_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 810 13 14, g32p_row02_traceSegment_004_0810_0013, g32p_row02_traceSegment_004_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 850 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 837 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 837 13 14, g32p_row02_traceSegment_004_0837_0013, g32p_row02_traceSegment_004_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 810 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 810 27 27, g32p_row02_traceSegment_004_0810_0027, g32p_row02_traceSegment_004_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 756 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 756 54 54, g32p_row02_traceSegment_004_0756_0054, g32p_row02_traceSegment_004_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 648 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 648 108 108, g32p_row02_traceSegment_004_0648_0108, g32p_row02_traceSegment_004_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 432 432 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 432 216 216, g32p_row02_traceSegment_004_0432_0216, g32p_row02_traceSegment_004_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_004 0 864 = [2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 432 432, g32p_row02_traceSegment_004_0000_0432, g32p_row02_traceSegment_004_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 864 13 14, g32p_row02_traceSegment_004_0864_0013, g32p_row02_traceSegment_004_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 891 13 14, g32p_row02_traceSegment_004_0891_0013, g32p_row02_traceSegment_004_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 864 27 27, g32p_row02_traceSegment_004_0864_0027, g32p_row02_traceSegment_004_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 918 13 14, g32p_row02_traceSegment_004_0918_0013, g32p_row02_traceSegment_004_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 945 13 14, g32p_row02_traceSegment_004_0945_0013, g32p_row02_traceSegment_004_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 918 27 27, g32p_row02_traceSegment_004_0918_0027, g32p_row02_traceSegment_004_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 864 54 54, g32p_row02_traceSegment_004_0864_0054, g32p_row02_traceSegment_004_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 972 13 14, g32p_row02_traceSegment_004_0972_0013, g32p_row02_traceSegment_004_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 999 13 14, g32p_row02_traceSegment_004_0999_0013, g32p_row02_traceSegment_004_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 972 27 27, g32p_row02_traceSegment_004_0972_0027, g32p_row02_traceSegment_004_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1026 13 14, g32p_row02_traceSegment_004_1026_0013, g32p_row02_traceSegment_004_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1053 13 14, g32p_row02_traceSegment_004_1053_0013, g32p_row02_traceSegment_004_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1026 27 27, g32p_row02_traceSegment_004_1026_0027, g32p_row02_traceSegment_004_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 972 54 54, g32p_row02_traceSegment_004_0972_0054, g32p_row02_traceSegment_004_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 864 108 108, g32p_row02_traceSegment_004_0864_0108, g32p_row02_traceSegment_004_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1080 13 14, g32p_row02_traceSegment_004_1080_0013, g32p_row02_traceSegment_004_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1107 13 14, g32p_row02_traceSegment_004_1107_0013, g32p_row02_traceSegment_004_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1080 27 27, g32p_row02_traceSegment_004_1080_0027, g32p_row02_traceSegment_004_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1134 13 14, g32p_row02_traceSegment_004_1134_0013, g32p_row02_traceSegment_004_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1161 13 14, g32p_row02_traceSegment_004_1161_0013, g32p_row02_traceSegment_004_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1134 27 27, g32p_row02_traceSegment_004_1134_0027, g32p_row02_traceSegment_004_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1080 54 54, g32p_row02_traceSegment_004_1080_0054, g32p_row02_traceSegment_004_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1188 13 14, g32p_row02_traceSegment_004_1188_0013, g32p_row02_traceSegment_004_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1215 13 14, g32p_row02_traceSegment_004_1215_0013, g32p_row02_traceSegment_004_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1188 27 27, g32p_row02_traceSegment_004_1188_0027, g32p_row02_traceSegment_004_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1242 13 14, g32p_row02_traceSegment_004_1242_0013, g32p_row02_traceSegment_004_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1269 13 14, g32p_row02_traceSegment_004_1269_0013, g32p_row02_traceSegment_004_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1242 27 27, g32p_row02_traceSegment_004_1242_0027, g32p_row02_traceSegment_004_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1188 54 54, g32p_row02_traceSegment_004_1188_0054, g32p_row02_traceSegment_004_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1080 108 108, g32p_row02_traceSegment_004_1080_0108, g32p_row02_traceSegment_004_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 864 216 216, g32p_row02_traceSegment_004_0864_0216, g32p_row02_traceSegment_004_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1296 13 14, g32p_row02_traceSegment_004_1296_0013, g32p_row02_traceSegment_004_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1323 13 14, g32p_row02_traceSegment_004_1323_0013, g32p_row02_traceSegment_004_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1296 27 27, g32p_row02_traceSegment_004_1296_0027, g32p_row02_traceSegment_004_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1350 13 14, g32p_row02_traceSegment_004_1350_0013, g32p_row02_traceSegment_004_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1377 13 14, g32p_row02_traceSegment_004_1377_0013, g32p_row02_traceSegment_004_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1350 27 27, g32p_row02_traceSegment_004_1350_0027, g32p_row02_traceSegment_004_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1296 54 54, g32p_row02_traceSegment_004_1296_0054, g32p_row02_traceSegment_004_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1404 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1404 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1404 13 14, g32p_row02_traceSegment_004_1404_0013, g32p_row02_traceSegment_004_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1431 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1431 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1431 13 14, g32p_row02_traceSegment_004_1431_0013, g32p_row02_traceSegment_004_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1404 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1404 27 27, g32p_row02_traceSegment_004_1404_0027, g32p_row02_traceSegment_004_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1458 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1458 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1458 13 14, g32p_row02_traceSegment_004_1458_0013, g32p_row02_traceSegment_004_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1485 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1498 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1485 27 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1485 13 14, g32p_row02_traceSegment_004_1485_0013, g32p_row02_traceSegment_004_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1458 54 = [1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1458 27 27, g32p_row02_traceSegment_004_1458_0027, g32p_row02_traceSegment_004_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1404 108 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1404 54 54, g32p_row02_traceSegment_004_1404_0054, g32p_row02_traceSegment_004_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 1296 216 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1296 108 108, g32p_row02_traceSegment_004_1296_0108, g32p_row02_traceSegment_004_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1512 13 14, g32p_row02_traceSegment_004_1512_0013, g32p_row02_traceSegment_004_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1539 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1539 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1539 13 14, g32p_row02_traceSegment_004_1539_0013, g32p_row02_traceSegment_004_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1512 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1512 27 27, g32p_row02_traceSegment_004_1512_0027, g32p_row02_traceSegment_004_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1566 13 14, g32p_row02_traceSegment_004_1566_0013, g32p_row02_traceSegment_004_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1593 13 14, g32p_row02_traceSegment_004_1593_0013, g32p_row02_traceSegment_004_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1566 27 27, g32p_row02_traceSegment_004_1566_0027, g32p_row02_traceSegment_004_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1512 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1512 54 54, g32p_row02_traceSegment_004_1512_0054, g32p_row02_traceSegment_004_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1620 13 14, g32p_row02_traceSegment_004_1620_0013, g32p_row02_traceSegment_004_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1647 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1647 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1647 13 14, g32p_row02_traceSegment_004_1647_0013, g32p_row02_traceSegment_004_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1620 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1620 27 27, g32p_row02_traceSegment_004_1620_0027, g32p_row02_traceSegment_004_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1674 13 14, g32p_row02_traceSegment_004_1674_0013, g32p_row02_traceSegment_004_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1701 13 14, g32p_row02_traceSegment_004_1701_0013, g32p_row02_traceSegment_004_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1674 27 27, g32p_row02_traceSegment_004_1674_0027, g32p_row02_traceSegment_004_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1620 54 54, g32p_row02_traceSegment_004_1620_0054, g32p_row02_traceSegment_004_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 1512 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1512 108 108, g32p_row02_traceSegment_004_1512_0108, g32p_row02_traceSegment_004_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 1296 432 = [3, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1296 216 216, g32p_row02_traceSegment_004_1296_0216, g32p_row02_traceSegment_004_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_004 864 864 = [3, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 864 432 432, g32p_row02_traceSegment_004_0864_0432, g32p_row02_traceSegment_004_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_004 0 1728 = [5, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 864 864, g32p_row02_traceSegment_004_0000_0864, g32p_row02_traceSegment_004_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1728 13 14, g32p_row02_traceSegment_004_1728_0013, g32p_row02_traceSegment_004_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1755 13 14, g32p_row02_traceSegment_004_1755_0013, g32p_row02_traceSegment_004_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1728 27 27, g32p_row02_traceSegment_004_1728_0027, g32p_row02_traceSegment_004_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1782 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1782 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1782 13 14, g32p_row02_traceSegment_004_1782_0013, g32p_row02_traceSegment_004_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1809 13 14, g32p_row02_traceSegment_004_1809_0013, g32p_row02_traceSegment_004_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1782 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1782 27 27, g32p_row02_traceSegment_004_1782_0027, g32p_row02_traceSegment_004_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1728 54 54, g32p_row02_traceSegment_004_1728_0054, g32p_row02_traceSegment_004_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1849 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1836 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1836 13 14, g32p_row02_traceSegment_004_1836_0013, g32p_row02_traceSegment_004_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1863 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1863 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1863 13 14, g32p_row02_traceSegment_004_1863_0013, g32p_row02_traceSegment_004_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1836 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1836 27 27, g32p_row02_traceSegment_004_1836_0027, g32p_row02_traceSegment_004_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1903 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1890 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1890 13 14, g32p_row02_traceSegment_004_1890_0013, g32p_row02_traceSegment_004_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1917 13 14, g32p_row02_traceSegment_004_1917_0013, g32p_row02_traceSegment_004_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1890 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1890 27 27, g32p_row02_traceSegment_004_1890_0027, g32p_row02_traceSegment_004_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1836 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1836 54 54, g32p_row02_traceSegment_004_1836_0054, g32p_row02_traceSegment_004_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1728 108 108, g32p_row02_traceSegment_004_1728_0108, g32p_row02_traceSegment_004_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1944 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1944 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1944 13 14, g32p_row02_traceSegment_004_1944_0013, g32p_row02_traceSegment_004_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1971 13 14, g32p_row02_traceSegment_004_1971_0013, g32p_row02_traceSegment_004_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1944 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1944 27 27, g32p_row02_traceSegment_004_1944_0027, g32p_row02_traceSegment_004_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1998 13 14, g32p_row02_traceSegment_004_1998_0013, g32p_row02_traceSegment_004_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2025 13 14, g32p_row02_traceSegment_004_2025_0013, g32p_row02_traceSegment_004_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1998 27 27, g32p_row02_traceSegment_004_1998_0027, g32p_row02_traceSegment_004_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 1944 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1944 54 54, g32p_row02_traceSegment_004_1944_0054, g32p_row02_traceSegment_004_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2052 13 14, g32p_row02_traceSegment_004_2052_0013, g32p_row02_traceSegment_004_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2079 13 14, g32p_row02_traceSegment_004_2079_0013, g32p_row02_traceSegment_004_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2052 27 27, g32p_row02_traceSegment_004_2052_0027, g32p_row02_traceSegment_004_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2106 13 14, g32p_row02_traceSegment_004_2106_0013, g32p_row02_traceSegment_004_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2133 13 14, g32p_row02_traceSegment_004_2133_0013, g32p_row02_traceSegment_004_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2106 27 27, g32p_row02_traceSegment_004_2106_0027, g32p_row02_traceSegment_004_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2052 54 54, g32p_row02_traceSegment_004_2052_0054, g32p_row02_traceSegment_004_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 1944 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1944 108 108, g32p_row02_traceSegment_004_1944_0108, g32p_row02_traceSegment_004_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 432 = [1, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1728 216 216, g32p_row02_traceSegment_004_1728_0216, g32p_row02_traceSegment_004_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2160 13 14, g32p_row02_traceSegment_004_2160_0013, g32p_row02_traceSegment_004_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2200 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2187 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2187 13 14, g32p_row02_traceSegment_004_2187_0013, g32p_row02_traceSegment_004_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2160 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2160 27 27, g32p_row02_traceSegment_004_2160_0027, g32p_row02_traceSegment_004_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2214 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2214 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2214 13 14, g32p_row02_traceSegment_004_2214_0013, g32p_row02_traceSegment_004_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2241 13 14, g32p_row02_traceSegment_004_2241_0013, g32p_row02_traceSegment_004_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2214 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2214 27 27, g32p_row02_traceSegment_004_2214_0027, g32p_row02_traceSegment_004_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2160 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2160 54 54, g32p_row02_traceSegment_004_2160_0054, g32p_row02_traceSegment_004_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2268 13 14, g32p_row02_traceSegment_004_2268_0013, g32p_row02_traceSegment_004_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2295 13 14, g32p_row02_traceSegment_004_2295_0013, g32p_row02_traceSegment_004_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2268 27 27, g32p_row02_traceSegment_004_2268_0027, g32p_row02_traceSegment_004_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2322 13 14, g32p_row02_traceSegment_004_2322_0013, g32p_row02_traceSegment_004_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2349 13 14, g32p_row02_traceSegment_004_2349_0013, g32p_row02_traceSegment_004_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2322 27 27, g32p_row02_traceSegment_004_2322_0027, g32p_row02_traceSegment_004_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2268 54 54, g32p_row02_traceSegment_004_2268_0054, g32p_row02_traceSegment_004_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 2160 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2160 108 108, g32p_row02_traceSegment_004_2160_0108, g32p_row02_traceSegment_004_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2376 13 14, g32p_row02_traceSegment_004_2376_0013, g32p_row02_traceSegment_004_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2403 13 14, g32p_row02_traceSegment_004_2403_0013, g32p_row02_traceSegment_004_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2376 27 27, g32p_row02_traceSegment_004_2376_0027, g32p_row02_traceSegment_004_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2430 13 14, g32p_row02_traceSegment_004_2430_0013, g32p_row02_traceSegment_004_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2457 13 14, g32p_row02_traceSegment_004_2457_0013, g32p_row02_traceSegment_004_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2430 27 27, g32p_row02_traceSegment_004_2430_0027, g32p_row02_traceSegment_004_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2376 54 54, g32p_row02_traceSegment_004_2376_0054, g32p_row02_traceSegment_004_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2484 13 14, g32p_row02_traceSegment_004_2484_0013, g32p_row02_traceSegment_004_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2524 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2511 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2511 13 14, g32p_row02_traceSegment_004_2511_0013, g32p_row02_traceSegment_004_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2484 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2484 27 27, g32p_row02_traceSegment_004_2484_0027, g32p_row02_traceSegment_004_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2538 13 14, g32p_row02_traceSegment_004_2538_0013, g32p_row02_traceSegment_004_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2565 13 14, g32p_row02_traceSegment_004_2565_0013, g32p_row02_traceSegment_004_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2538 27 27, g32p_row02_traceSegment_004_2538_0027, g32p_row02_traceSegment_004_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2484 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2484 54 54, g32p_row02_traceSegment_004_2484_0054, g32p_row02_traceSegment_004_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 2376 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2376 108 108, g32p_row02_traceSegment_004_2376_0108, g32p_row02_traceSegment_004_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 2160 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2160 216 216, g32p_row02_traceSegment_004_2160_0216, g32p_row02_traceSegment_004_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 864 = [1, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1728 432 432, g32p_row02_traceSegment_004_1728_0432, g32p_row02_traceSegment_004_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2592 13 14, g32p_row02_traceSegment_004_2592_0013, g32p_row02_traceSegment_004_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2619 13 14, g32p_row02_traceSegment_004_2619_0013, g32p_row02_traceSegment_004_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2592 27 27, g32p_row02_traceSegment_004_2592_0027, g32p_row02_traceSegment_004_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2646 13 14, g32p_row02_traceSegment_004_2646_0013, g32p_row02_traceSegment_004_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2673 13 14, g32p_row02_traceSegment_004_2673_0013, g32p_row02_traceSegment_004_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2646 27 27, g32p_row02_traceSegment_004_2646_0027, g32p_row02_traceSegment_004_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2592 54 54, g32p_row02_traceSegment_004_2592_0054, g32p_row02_traceSegment_004_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2700 13 14, g32p_row02_traceSegment_004_2700_0013, g32p_row02_traceSegment_004_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2727 13 14, g32p_row02_traceSegment_004_2727_0013, g32p_row02_traceSegment_004_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2700 27 27, g32p_row02_traceSegment_004_2700_0027, g32p_row02_traceSegment_004_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2754 13 14, g32p_row02_traceSegment_004_2754_0013, g32p_row02_traceSegment_004_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2781 13 14, g32p_row02_traceSegment_004_2781_0013, g32p_row02_traceSegment_004_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2754 27 27, g32p_row02_traceSegment_004_2754_0027, g32p_row02_traceSegment_004_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2700 54 54, g32p_row02_traceSegment_004_2700_0054, g32p_row02_traceSegment_004_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2592 108 108, g32p_row02_traceSegment_004_2592_0108, g32p_row02_traceSegment_004_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2808 13 14, g32p_row02_traceSegment_004_2808_0013, g32p_row02_traceSegment_004_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2835 13 14, g32p_row02_traceSegment_004_2835_0013, g32p_row02_traceSegment_004_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2808 27 27, g32p_row02_traceSegment_004_2808_0027, g32p_row02_traceSegment_004_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2862 13 14, g32p_row02_traceSegment_004_2862_0013, g32p_row02_traceSegment_004_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2889 13 14, g32p_row02_traceSegment_004_2889_0013, g32p_row02_traceSegment_004_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2862 27 27, g32p_row02_traceSegment_004_2862_0027, g32p_row02_traceSegment_004_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2808 54 54, g32p_row02_traceSegment_004_2808_0054, g32p_row02_traceSegment_004_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2916 13 14, g32p_row02_traceSegment_004_2916_0013, g32p_row02_traceSegment_004_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2943 13 14, g32p_row02_traceSegment_004_2943_0013, g32p_row02_traceSegment_004_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2916 27 27, g32p_row02_traceSegment_004_2916_0027, g32p_row02_traceSegment_004_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2970 13 14, g32p_row02_traceSegment_004_2970_0013, g32p_row02_traceSegment_004_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2997 13 14, g32p_row02_traceSegment_004_2997_0013, g32p_row02_traceSegment_004_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2970 27 27, g32p_row02_traceSegment_004_2970_0027, g32p_row02_traceSegment_004_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2916 54 54, g32p_row02_traceSegment_004_2916_0054, g32p_row02_traceSegment_004_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2808 108 108, g32p_row02_traceSegment_004_2808_0108, g32p_row02_traceSegment_004_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2592 216 216, g32p_row02_traceSegment_004_2592_0216, g32p_row02_traceSegment_004_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3024 13 14, g32p_row02_traceSegment_004_3024_0013, g32p_row02_traceSegment_004_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3051 13 14, g32p_row02_traceSegment_004_3051_0013, g32p_row02_traceSegment_004_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3024 27 27, g32p_row02_traceSegment_004_3024_0027, g32p_row02_traceSegment_004_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3078 13 14, g32p_row02_traceSegment_004_3078_0013, g32p_row02_traceSegment_004_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3105 13 14, g32p_row02_traceSegment_004_3105_0013, g32p_row02_traceSegment_004_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3078 27 27, g32p_row02_traceSegment_004_3078_0027, g32p_row02_traceSegment_004_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3024 54 54, g32p_row02_traceSegment_004_3024_0054, g32p_row02_traceSegment_004_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3132 13 14, g32p_row02_traceSegment_004_3132_0013, g32p_row02_traceSegment_004_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3159 13 14, g32p_row02_traceSegment_004_3159_0013, g32p_row02_traceSegment_004_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3132 27 27, g32p_row02_traceSegment_004_3132_0027, g32p_row02_traceSegment_004_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3186 13 14, g32p_row02_traceSegment_004_3186_0013, g32p_row02_traceSegment_004_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3213 13 14, g32p_row02_traceSegment_004_3213_0013, g32p_row02_traceSegment_004_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3186 27 27, g32p_row02_traceSegment_004_3186_0027, g32p_row02_traceSegment_004_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3132 54 54, g32p_row02_traceSegment_004_3132_0054, g32p_row02_traceSegment_004_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3024 108 108, g32p_row02_traceSegment_004_3024_0108, g32p_row02_traceSegment_004_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3240 13 14, g32p_row02_traceSegment_004_3240_0013, g32p_row02_traceSegment_004_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3267 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3280 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3267 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3267 13 14, g32p_row02_traceSegment_004_3267_0013, g32p_row02_traceSegment_004_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3240 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3240 27 27, g32p_row02_traceSegment_004_3240_0027, g32p_row02_traceSegment_004_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3294 13 14, g32p_row02_traceSegment_004_3294_0013, g32p_row02_traceSegment_004_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3321 13 14, g32p_row02_traceSegment_004_3321_0013, g32p_row02_traceSegment_004_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3294 27 27, g32p_row02_traceSegment_004_3294_0027, g32p_row02_traceSegment_004_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 3240 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3240 54 54, g32p_row02_traceSegment_004_3240_0054, g32p_row02_traceSegment_004_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3348 13 14, g32p_row02_traceSegment_004_3348_0013, g32p_row02_traceSegment_004_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3388 14 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3375 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3375 13 14, g32p_row02_traceSegment_004_3375_0013, g32p_row02_traceSegment_004_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3348 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3348 27 27, g32p_row02_traceSegment_004_3348_0027, g32p_row02_traceSegment_004_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3402 13 = [5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3402 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3402 13 14, g32p_row02_traceSegment_004_3402_0013, g32p_row02_traceSegment_004_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_004 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_004 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_004_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_004 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3429 13 14, g32p_row02_traceSegment_004_3429_0013, g32p_row02_traceSegment_004_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_004 3402 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3402 27 27, g32p_row02_traceSegment_004_3402_0027, g32p_row02_traceSegment_004_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_004 3348 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3348 54 54, g32p_row02_traceSegment_004_3348_0054, g32p_row02_traceSegment_004_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_004 3240 216 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3240 108 108, g32p_row02_traceSegment_004_3240_0108, g32p_row02_traceSegment_004_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_004_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_004 3024 432 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 3024 216 216, g32p_row02_traceSegment_004_3024_0216, g32p_row02_traceSegment_004_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_004_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_004 2592 864 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 2592 432 432, g32p_row02_traceSegment_004_2592_0432, g32p_row02_traceSegment_004_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_004_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_004 1728 1728 = [11, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 1728 864 864, g32p_row02_traceSegment_004_1728_0864, g32p_row02_traceSegment_004_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_004_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_004 0 3456 = [16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_004 0 1728 1728, g32p_row02_traceSegment_004_0000_1728, g32p_row02_traceSegment_004_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_004 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 4 = [16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_004_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_005 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 5 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_005_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 13 14, g32p_row02_traceSegment_005_0000_0013, g32p_row02_traceSegment_005_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 27 13 14, g32p_row02_traceSegment_005_0027_0013, g32p_row02_traceSegment_005_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 27 27, g32p_row02_traceSegment_005_0000_0027, g32p_row02_traceSegment_005_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 54 13 14, g32p_row02_traceSegment_005_0054_0013, g32p_row02_traceSegment_005_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 81 13 14, g32p_row02_traceSegment_005_0081_0013, g32p_row02_traceSegment_005_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 54 27 27, g32p_row02_traceSegment_005_0054_0027, g32p_row02_traceSegment_005_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 54 54, g32p_row02_traceSegment_005_0000_0054, g32p_row02_traceSegment_005_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 108 13 14, g32p_row02_traceSegment_005_0108_0013, g32p_row02_traceSegment_005_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 135 13 14, g32p_row02_traceSegment_005_0135_0013, g32p_row02_traceSegment_005_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 108 27 27, g32p_row02_traceSegment_005_0108_0027, g32p_row02_traceSegment_005_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 162 13 14, g32p_row02_traceSegment_005_0162_0013, g32p_row02_traceSegment_005_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 189 13 14, g32p_row02_traceSegment_005_0189_0013, g32p_row02_traceSegment_005_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 162 27 27, g32p_row02_traceSegment_005_0162_0027, g32p_row02_traceSegment_005_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 108 54 54, g32p_row02_traceSegment_005_0108_0054, g32p_row02_traceSegment_005_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 108 108, g32p_row02_traceSegment_005_0000_0108, g32p_row02_traceSegment_005_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 216 13 14, g32p_row02_traceSegment_005_0216_0013, g32p_row02_traceSegment_005_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 243 13 14, g32p_row02_traceSegment_005_0243_0013, g32p_row02_traceSegment_005_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 216 27 27, g32p_row02_traceSegment_005_0216_0027, g32p_row02_traceSegment_005_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 270 13 14, g32p_row02_traceSegment_005_0270_0013, g32p_row02_traceSegment_005_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 297 13 14, g32p_row02_traceSegment_005_0297_0013, g32p_row02_traceSegment_005_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 270 27 27, g32p_row02_traceSegment_005_0270_0027, g32p_row02_traceSegment_005_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 216 54 54, g32p_row02_traceSegment_005_0216_0054, g32p_row02_traceSegment_005_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 324 13 14, g32p_row02_traceSegment_005_0324_0013, g32p_row02_traceSegment_005_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 351 13 14, g32p_row02_traceSegment_005_0351_0013, g32p_row02_traceSegment_005_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 324 27 27, g32p_row02_traceSegment_005_0324_0027, g32p_row02_traceSegment_005_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 378 13 14, g32p_row02_traceSegment_005_0378_0013, g32p_row02_traceSegment_005_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 405 13 14, g32p_row02_traceSegment_005_0405_0013, g32p_row02_traceSegment_005_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 378 27 27, g32p_row02_traceSegment_005_0378_0027, g32p_row02_traceSegment_005_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 324 54 54, g32p_row02_traceSegment_005_0324_0054, g32p_row02_traceSegment_005_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 216 108 108, g32p_row02_traceSegment_005_0216_0108, g32p_row02_traceSegment_005_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 216 216, g32p_row02_traceSegment_005_0000_0216, g32p_row02_traceSegment_005_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 432 13 14, g32p_row02_traceSegment_005_0432_0013, g32p_row02_traceSegment_005_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 459 13 14, g32p_row02_traceSegment_005_0459_0013, g32p_row02_traceSegment_005_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 432 27 27, g32p_row02_traceSegment_005_0432_0027, g32p_row02_traceSegment_005_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 486 13 14, g32p_row02_traceSegment_005_0486_0013, g32p_row02_traceSegment_005_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 513 13 14, g32p_row02_traceSegment_005_0513_0013, g32p_row02_traceSegment_005_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 486 27 27, g32p_row02_traceSegment_005_0486_0027, g32p_row02_traceSegment_005_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 432 54 54, g32p_row02_traceSegment_005_0432_0054, g32p_row02_traceSegment_005_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 540 13 14, g32p_row02_traceSegment_005_0540_0013, g32p_row02_traceSegment_005_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 567 13 14, g32p_row02_traceSegment_005_0567_0013, g32p_row02_traceSegment_005_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 540 27 27, g32p_row02_traceSegment_005_0540_0027, g32p_row02_traceSegment_005_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 594 13 14, g32p_row02_traceSegment_005_0594_0013, g32p_row02_traceSegment_005_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 621 13 14, g32p_row02_traceSegment_005_0621_0013, g32p_row02_traceSegment_005_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 594 27 27, g32p_row02_traceSegment_005_0594_0027, g32p_row02_traceSegment_005_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 540 54 54, g32p_row02_traceSegment_005_0540_0054, g32p_row02_traceSegment_005_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 432 108 108, g32p_row02_traceSegment_005_0432_0108, g32p_row02_traceSegment_005_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 648 13 14, g32p_row02_traceSegment_005_0648_0013, g32p_row02_traceSegment_005_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 675 13 14, g32p_row02_traceSegment_005_0675_0013, g32p_row02_traceSegment_005_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 648 27 27, g32p_row02_traceSegment_005_0648_0027, g32p_row02_traceSegment_005_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 702 13 14, g32p_row02_traceSegment_005_0702_0013, g32p_row02_traceSegment_005_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 729 13 14, g32p_row02_traceSegment_005_0729_0013, g32p_row02_traceSegment_005_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 702 27 27, g32p_row02_traceSegment_005_0702_0027, g32p_row02_traceSegment_005_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 648 54 54, g32p_row02_traceSegment_005_0648_0054, g32p_row02_traceSegment_005_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 756 13 14, g32p_row02_traceSegment_005_0756_0013, g32p_row02_traceSegment_005_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 783 13 14, g32p_row02_traceSegment_005_0783_0013, g32p_row02_traceSegment_005_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 756 27 27, g32p_row02_traceSegment_005_0756_0027, g32p_row02_traceSegment_005_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 810 13 14, g32p_row02_traceSegment_005_0810_0013, g32p_row02_traceSegment_005_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 837 13 14, g32p_row02_traceSegment_005_0837_0013, g32p_row02_traceSegment_005_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 810 27 27, g32p_row02_traceSegment_005_0810_0027, g32p_row02_traceSegment_005_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 756 54 54, g32p_row02_traceSegment_005_0756_0054, g32p_row02_traceSegment_005_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 648 108 108, g32p_row02_traceSegment_005_0648_0108, g32p_row02_traceSegment_005_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 432 216 216, g32p_row02_traceSegment_005_0432_0216, g32p_row02_traceSegment_005_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_005 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 432 432, g32p_row02_traceSegment_005_0000_0432, g32p_row02_traceSegment_005_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 864 13 14, g32p_row02_traceSegment_005_0864_0013, g32p_row02_traceSegment_005_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 891 13 14, g32p_row02_traceSegment_005_0891_0013, g32p_row02_traceSegment_005_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 864 27 27, g32p_row02_traceSegment_005_0864_0027, g32p_row02_traceSegment_005_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 918 13 14, g32p_row02_traceSegment_005_0918_0013, g32p_row02_traceSegment_005_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 945 13 14, g32p_row02_traceSegment_005_0945_0013, g32p_row02_traceSegment_005_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 918 27 27, g32p_row02_traceSegment_005_0918_0027, g32p_row02_traceSegment_005_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 864 54 54, g32p_row02_traceSegment_005_0864_0054, g32p_row02_traceSegment_005_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 972 13 14, g32p_row02_traceSegment_005_0972_0013, g32p_row02_traceSegment_005_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 999 13 14, g32p_row02_traceSegment_005_0999_0013, g32p_row02_traceSegment_005_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 972 27 27, g32p_row02_traceSegment_005_0972_0027, g32p_row02_traceSegment_005_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1026 13 14, g32p_row02_traceSegment_005_1026_0013, g32p_row02_traceSegment_005_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1053 13 14, g32p_row02_traceSegment_005_1053_0013, g32p_row02_traceSegment_005_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1026 27 27, g32p_row02_traceSegment_005_1026_0027, g32p_row02_traceSegment_005_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 972 54 54, g32p_row02_traceSegment_005_0972_0054, g32p_row02_traceSegment_005_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 864 108 108, g32p_row02_traceSegment_005_0864_0108, g32p_row02_traceSegment_005_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1080 13 14, g32p_row02_traceSegment_005_1080_0013, g32p_row02_traceSegment_005_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1107 13 14, g32p_row02_traceSegment_005_1107_0013, g32p_row02_traceSegment_005_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1080 27 27, g32p_row02_traceSegment_005_1080_0027, g32p_row02_traceSegment_005_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1134 13 14, g32p_row02_traceSegment_005_1134_0013, g32p_row02_traceSegment_005_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1161 13 14, g32p_row02_traceSegment_005_1161_0013, g32p_row02_traceSegment_005_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1134 27 27, g32p_row02_traceSegment_005_1134_0027, g32p_row02_traceSegment_005_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1080 54 54, g32p_row02_traceSegment_005_1080_0054, g32p_row02_traceSegment_005_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1188 13 14, g32p_row02_traceSegment_005_1188_0013, g32p_row02_traceSegment_005_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1215 13 14, g32p_row02_traceSegment_005_1215_0013, g32p_row02_traceSegment_005_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1188 27 27, g32p_row02_traceSegment_005_1188_0027, g32p_row02_traceSegment_005_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1242 13 14, g32p_row02_traceSegment_005_1242_0013, g32p_row02_traceSegment_005_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1269 13 14, g32p_row02_traceSegment_005_1269_0013, g32p_row02_traceSegment_005_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1242 27 27, g32p_row02_traceSegment_005_1242_0027, g32p_row02_traceSegment_005_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1188 54 54, g32p_row02_traceSegment_005_1188_0054, g32p_row02_traceSegment_005_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1080 108 108, g32p_row02_traceSegment_005_1080_0108, g32p_row02_traceSegment_005_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 864 216 216, g32p_row02_traceSegment_005_0864_0216, g32p_row02_traceSegment_005_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1296 13 14, g32p_row02_traceSegment_005_1296_0013, g32p_row02_traceSegment_005_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1323 13 14, g32p_row02_traceSegment_005_1323_0013, g32p_row02_traceSegment_005_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1296 27 27, g32p_row02_traceSegment_005_1296_0027, g32p_row02_traceSegment_005_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1350 13 14, g32p_row02_traceSegment_005_1350_0013, g32p_row02_traceSegment_005_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1377 13 14, g32p_row02_traceSegment_005_1377_0013, g32p_row02_traceSegment_005_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1350 27 27, g32p_row02_traceSegment_005_1350_0027, g32p_row02_traceSegment_005_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1296 54 54, g32p_row02_traceSegment_005_1296_0054, g32p_row02_traceSegment_005_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1404 13 14, g32p_row02_traceSegment_005_1404_0013, g32p_row02_traceSegment_005_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1431 13 14, g32p_row02_traceSegment_005_1431_0013, g32p_row02_traceSegment_005_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1404 27 27, g32p_row02_traceSegment_005_1404_0027, g32p_row02_traceSegment_005_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1458 13 14, g32p_row02_traceSegment_005_1458_0013, g32p_row02_traceSegment_005_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1485 13 14, g32p_row02_traceSegment_005_1485_0013, g32p_row02_traceSegment_005_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1458 27 27, g32p_row02_traceSegment_005_1458_0027, g32p_row02_traceSegment_005_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1404 54 54, g32p_row02_traceSegment_005_1404_0054, g32p_row02_traceSegment_005_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1296 108 108, g32p_row02_traceSegment_005_1296_0108, g32p_row02_traceSegment_005_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1512 13 14, g32p_row02_traceSegment_005_1512_0013, g32p_row02_traceSegment_005_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1539 13 14, g32p_row02_traceSegment_005_1539_0013, g32p_row02_traceSegment_005_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1512 27 27, g32p_row02_traceSegment_005_1512_0027, g32p_row02_traceSegment_005_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1566 13 14, g32p_row02_traceSegment_005_1566_0013, g32p_row02_traceSegment_005_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1593 13 14, g32p_row02_traceSegment_005_1593_0013, g32p_row02_traceSegment_005_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1566 27 27, g32p_row02_traceSegment_005_1566_0027, g32p_row02_traceSegment_005_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1512 54 54, g32p_row02_traceSegment_005_1512_0054, g32p_row02_traceSegment_005_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1620 13 14, g32p_row02_traceSegment_005_1620_0013, g32p_row02_traceSegment_005_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1647 13 14, g32p_row02_traceSegment_005_1647_0013, g32p_row02_traceSegment_005_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1620 27 27, g32p_row02_traceSegment_005_1620_0027, g32p_row02_traceSegment_005_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1674 13 14, g32p_row02_traceSegment_005_1674_0013, g32p_row02_traceSegment_005_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1701 13 14, g32p_row02_traceSegment_005_1701_0013, g32p_row02_traceSegment_005_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1674 27 27, g32p_row02_traceSegment_005_1674_0027, g32p_row02_traceSegment_005_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1620 54 54, g32p_row02_traceSegment_005_1620_0054, g32p_row02_traceSegment_005_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1512 108 108, g32p_row02_traceSegment_005_1512_0108, g32p_row02_traceSegment_005_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1296 216 216, g32p_row02_traceSegment_005_1296_0216, g32p_row02_traceSegment_005_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_005 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 864 432 432, g32p_row02_traceSegment_005_0864_0432, g32p_row02_traceSegment_005_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_005 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 864 864, g32p_row02_traceSegment_005_0000_0864, g32p_row02_traceSegment_005_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1728 13 14, g32p_row02_traceSegment_005_1728_0013, g32p_row02_traceSegment_005_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1755 13 14, g32p_row02_traceSegment_005_1755_0013, g32p_row02_traceSegment_005_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1728 27 27, g32p_row02_traceSegment_005_1728_0027, g32p_row02_traceSegment_005_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1782 13 14, g32p_row02_traceSegment_005_1782_0013, g32p_row02_traceSegment_005_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1809 13 14, g32p_row02_traceSegment_005_1809_0013, g32p_row02_traceSegment_005_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1782 27 27, g32p_row02_traceSegment_005_1782_0027, g32p_row02_traceSegment_005_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1728 54 54, g32p_row02_traceSegment_005_1728_0054, g32p_row02_traceSegment_005_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1836 13 14, g32p_row02_traceSegment_005_1836_0013, g32p_row02_traceSegment_005_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1863 13 14, g32p_row02_traceSegment_005_1863_0013, g32p_row02_traceSegment_005_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1836 27 27, g32p_row02_traceSegment_005_1836_0027, g32p_row02_traceSegment_005_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1890 13 14, g32p_row02_traceSegment_005_1890_0013, g32p_row02_traceSegment_005_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1917 13 14, g32p_row02_traceSegment_005_1917_0013, g32p_row02_traceSegment_005_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1890 27 27, g32p_row02_traceSegment_005_1890_0027, g32p_row02_traceSegment_005_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1836 54 54, g32p_row02_traceSegment_005_1836_0054, g32p_row02_traceSegment_005_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1728 108 108, g32p_row02_traceSegment_005_1728_0108, g32p_row02_traceSegment_005_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1944 13 14, g32p_row02_traceSegment_005_1944_0013, g32p_row02_traceSegment_005_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1971 13 14, g32p_row02_traceSegment_005_1971_0013, g32p_row02_traceSegment_005_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1944 27 27, g32p_row02_traceSegment_005_1944_0027, g32p_row02_traceSegment_005_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1998 13 14, g32p_row02_traceSegment_005_1998_0013, g32p_row02_traceSegment_005_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2025 13 14, g32p_row02_traceSegment_005_2025_0013, g32p_row02_traceSegment_005_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1998 27 27, g32p_row02_traceSegment_005_1998_0027, g32p_row02_traceSegment_005_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1944 54 54, g32p_row02_traceSegment_005_1944_0054, g32p_row02_traceSegment_005_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2052 13 14, g32p_row02_traceSegment_005_2052_0013, g32p_row02_traceSegment_005_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2079 13 14, g32p_row02_traceSegment_005_2079_0013, g32p_row02_traceSegment_005_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2052 27 27, g32p_row02_traceSegment_005_2052_0027, g32p_row02_traceSegment_005_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2106 13 14, g32p_row02_traceSegment_005_2106_0013, g32p_row02_traceSegment_005_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2133 13 14, g32p_row02_traceSegment_005_2133_0013, g32p_row02_traceSegment_005_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2106 27 27, g32p_row02_traceSegment_005_2106_0027, g32p_row02_traceSegment_005_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2052 54 54, g32p_row02_traceSegment_005_2052_0054, g32p_row02_traceSegment_005_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1944 108 108, g32p_row02_traceSegment_005_1944_0108, g32p_row02_traceSegment_005_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1728 216 216, g32p_row02_traceSegment_005_1728_0216, g32p_row02_traceSegment_005_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2160 13 14, g32p_row02_traceSegment_005_2160_0013, g32p_row02_traceSegment_005_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2187 13 14, g32p_row02_traceSegment_005_2187_0013, g32p_row02_traceSegment_005_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2160 27 27, g32p_row02_traceSegment_005_2160_0027, g32p_row02_traceSegment_005_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2214 13 14, g32p_row02_traceSegment_005_2214_0013, g32p_row02_traceSegment_005_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2241 13 14, g32p_row02_traceSegment_005_2241_0013, g32p_row02_traceSegment_005_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2214 27 27, g32p_row02_traceSegment_005_2214_0027, g32p_row02_traceSegment_005_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2160 54 54, g32p_row02_traceSegment_005_2160_0054, g32p_row02_traceSegment_005_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2268 13 14, g32p_row02_traceSegment_005_2268_0013, g32p_row02_traceSegment_005_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2295 13 14, g32p_row02_traceSegment_005_2295_0013, g32p_row02_traceSegment_005_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2268 27 27, g32p_row02_traceSegment_005_2268_0027, g32p_row02_traceSegment_005_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2322 13 14, g32p_row02_traceSegment_005_2322_0013, g32p_row02_traceSegment_005_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2349 13 14, g32p_row02_traceSegment_005_2349_0013, g32p_row02_traceSegment_005_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2322 27 27, g32p_row02_traceSegment_005_2322_0027, g32p_row02_traceSegment_005_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2268 54 54, g32p_row02_traceSegment_005_2268_0054, g32p_row02_traceSegment_005_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2160 108 108, g32p_row02_traceSegment_005_2160_0108, g32p_row02_traceSegment_005_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2376 13 14, g32p_row02_traceSegment_005_2376_0013, g32p_row02_traceSegment_005_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2403 13 14, g32p_row02_traceSegment_005_2403_0013, g32p_row02_traceSegment_005_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2376 27 27, g32p_row02_traceSegment_005_2376_0027, g32p_row02_traceSegment_005_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2430 13 14, g32p_row02_traceSegment_005_2430_0013, g32p_row02_traceSegment_005_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2457 13 14, g32p_row02_traceSegment_005_2457_0013, g32p_row02_traceSegment_005_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2430 27 27, g32p_row02_traceSegment_005_2430_0027, g32p_row02_traceSegment_005_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2376 54 54, g32p_row02_traceSegment_005_2376_0054, g32p_row02_traceSegment_005_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2484 13 14, g32p_row02_traceSegment_005_2484_0013, g32p_row02_traceSegment_005_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2511 13 14, g32p_row02_traceSegment_005_2511_0013, g32p_row02_traceSegment_005_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2484 27 27, g32p_row02_traceSegment_005_2484_0027, g32p_row02_traceSegment_005_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2538 13 14, g32p_row02_traceSegment_005_2538_0013, g32p_row02_traceSegment_005_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2565 13 14, g32p_row02_traceSegment_005_2565_0013, g32p_row02_traceSegment_005_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2538 27 27, g32p_row02_traceSegment_005_2538_0027, g32p_row02_traceSegment_005_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2484 54 54, g32p_row02_traceSegment_005_2484_0054, g32p_row02_traceSegment_005_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2376 108 108, g32p_row02_traceSegment_005_2376_0108, g32p_row02_traceSegment_005_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2160 216 216, g32p_row02_traceSegment_005_2160_0216, g32p_row02_traceSegment_005_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1728 432 432, g32p_row02_traceSegment_005_1728_0432, g32p_row02_traceSegment_005_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2592 13 14, g32p_row02_traceSegment_005_2592_0013, g32p_row02_traceSegment_005_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2619 13 14, g32p_row02_traceSegment_005_2619_0013, g32p_row02_traceSegment_005_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2592 27 27, g32p_row02_traceSegment_005_2592_0027, g32p_row02_traceSegment_005_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2659 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2646 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2646 13 14, g32p_row02_traceSegment_005_2646_0013, g32p_row02_traceSegment_005_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2673 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2686 14 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2673 27 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2673 13 14, g32p_row02_traceSegment_005_2673_0013, g32p_row02_traceSegment_005_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2646 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2646 27 27, g32p_row02_traceSegment_005_2646_0027, g32p_row02_traceSegment_005_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2592 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2592 54 54, g32p_row02_traceSegment_005_2592_0054, g32p_row02_traceSegment_005_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2700 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2700 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2700 13 14, g32p_row02_traceSegment_005_2700_0013, g32p_row02_traceSegment_005_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2727 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2727 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2727 13 14, g32p_row02_traceSegment_005_2727_0013, g32p_row02_traceSegment_005_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2700 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2700 27 27, g32p_row02_traceSegment_005_2700_0027, g32p_row02_traceSegment_005_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2754 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2754 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2754 13 14, g32p_row02_traceSegment_005_2754_0013, g32p_row02_traceSegment_005_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2781 13 14, g32p_row02_traceSegment_005_2781_0013, g32p_row02_traceSegment_005_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2754 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2754 27 27, g32p_row02_traceSegment_005_2754_0027, g32p_row02_traceSegment_005_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2700 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2700 54 54, g32p_row02_traceSegment_005_2700_0054, g32p_row02_traceSegment_005_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 2592 216 = [10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2592 108 108, g32p_row02_traceSegment_005_2592_0108, g32p_row02_traceSegment_005_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2808 13 14, g32p_row02_traceSegment_005_2808_0013, g32p_row02_traceSegment_005_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2835 13 14, g32p_row02_traceSegment_005_2835_0013, g32p_row02_traceSegment_005_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2808 27 27, g32p_row02_traceSegment_005_2808_0027, g32p_row02_traceSegment_005_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2862 13 14, g32p_row02_traceSegment_005_2862_0013, g32p_row02_traceSegment_005_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2889 13 14, g32p_row02_traceSegment_005_2889_0013, g32p_row02_traceSegment_005_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2862 27 27, g32p_row02_traceSegment_005_2862_0027, g32p_row02_traceSegment_005_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2808 54 54, g32p_row02_traceSegment_005_2808_0054, g32p_row02_traceSegment_005_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2916 13 14, g32p_row02_traceSegment_005_2916_0013, g32p_row02_traceSegment_005_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2943 13 14, g32p_row02_traceSegment_005_2943_0013, g32p_row02_traceSegment_005_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2916 27 27, g32p_row02_traceSegment_005_2916_0027, g32p_row02_traceSegment_005_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2970 13 14, g32p_row02_traceSegment_005_2970_0013, g32p_row02_traceSegment_005_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 2997 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 2997 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2997 13 14, g32p_row02_traceSegment_005_2997_0013, g32p_row02_traceSegment_005_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 2970 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2970 27 27, g32p_row02_traceSegment_005_2970_0027, g32p_row02_traceSegment_005_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 2916 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2916 54 54, g32p_row02_traceSegment_005_2916_0054, g32p_row02_traceSegment_005_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 2808 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2808 108 108, g32p_row02_traceSegment_005_2808_0108, g32p_row02_traceSegment_005_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 2592 432 = [11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2592 216 216, g32p_row02_traceSegment_005_2592_0216, g32p_row02_traceSegment_005_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3024 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3024 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3024 13 14, g32p_row02_traceSegment_005_3024_0013, g32p_row02_traceSegment_005_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3051 13 14, g32p_row02_traceSegment_005_3051_0013, g32p_row02_traceSegment_005_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3024 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3024 27 27, g32p_row02_traceSegment_005_3024_0027, g32p_row02_traceSegment_005_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3078 13 14, g32p_row02_traceSegment_005_3078_0013, g32p_row02_traceSegment_005_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3105 13 14, g32p_row02_traceSegment_005_3105_0013, g32p_row02_traceSegment_005_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3078 27 27, g32p_row02_traceSegment_005_3078_0027, g32p_row02_traceSegment_005_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 3024 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3024 54 54, g32p_row02_traceSegment_005_3024_0054, g32p_row02_traceSegment_005_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3132 13 14, g32p_row02_traceSegment_005_3132_0013, g32p_row02_traceSegment_005_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3159 13 14, g32p_row02_traceSegment_005_3159_0013, g32p_row02_traceSegment_005_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3132 27 27, g32p_row02_traceSegment_005_3132_0027, g32p_row02_traceSegment_005_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3186 13 14, g32p_row02_traceSegment_005_3186_0013, g32p_row02_traceSegment_005_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3213 13 14, g32p_row02_traceSegment_005_3213_0013, g32p_row02_traceSegment_005_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3186 27 27, g32p_row02_traceSegment_005_3186_0027, g32p_row02_traceSegment_005_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3132 54 54, g32p_row02_traceSegment_005_3132_0054, g32p_row02_traceSegment_005_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 3024 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3024 108 108, g32p_row02_traceSegment_005_3024_0108, g32p_row02_traceSegment_005_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3240 13 14, g32p_row02_traceSegment_005_3240_0013, g32p_row02_traceSegment_005_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3267 13 14, g32p_row02_traceSegment_005_3267_0013, g32p_row02_traceSegment_005_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3240 27 27, g32p_row02_traceSegment_005_3240_0027, g32p_row02_traceSegment_005_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3294 13 14, g32p_row02_traceSegment_005_3294_0013, g32p_row02_traceSegment_005_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3321 13 14, g32p_row02_traceSegment_005_3321_0013, g32p_row02_traceSegment_005_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3294 27 27, g32p_row02_traceSegment_005_3294_0027, g32p_row02_traceSegment_005_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3240 54 54, g32p_row02_traceSegment_005_3240_0054, g32p_row02_traceSegment_005_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3348 13 14, g32p_row02_traceSegment_005_3348_0013, g32p_row02_traceSegment_005_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3375 13 14, g32p_row02_traceSegment_005_3375_0013, g32p_row02_traceSegment_005_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3348 27 27, g32p_row02_traceSegment_005_3348_0027, g32p_row02_traceSegment_005_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3402 13 14, g32p_row02_traceSegment_005_3402_0013, g32p_row02_traceSegment_005_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_005 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_005 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_005_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_005 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3429 13 14, g32p_row02_traceSegment_005_3429_0013, g32p_row02_traceSegment_005_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_005 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3402 27 27, g32p_row02_traceSegment_005_3402_0027, g32p_row02_traceSegment_005_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_005 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3348 54 54, g32p_row02_traceSegment_005_3348_0054, g32p_row02_traceSegment_005_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_005 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3240 108 108, g32p_row02_traceSegment_005_3240_0108, g32p_row02_traceSegment_005_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_005_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_005 3024 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 3024 216 216, g32p_row02_traceSegment_005_3024_0216, g32p_row02_traceSegment_005_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_005_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_005 2592 864 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 2592 432 432, g32p_row02_traceSegment_005_2592_0432, g32p_row02_traceSegment_005_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_005_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_005 1728 1728 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 1728 864 864, g32p_row02_traceSegment_005_1728_0864, g32p_row02_traceSegment_005_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_005_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_005 0 3456 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_005 0 1728 1728, g32p_row02_traceSegment_005_0000_1728, g32p_row02_traceSegment_005_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_005 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 5 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_005_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_006 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 6 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_006_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 13 14, g32p_row02_traceSegment_006_0000_0013, g32p_row02_traceSegment_006_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 40 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 27 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 27 13 14, g32p_row02_traceSegment_006_0027_0013, g32p_row02_traceSegment_006_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 0 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 27 27, g32p_row02_traceSegment_006_0000_0027, g32p_row02_traceSegment_006_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 54 13 14, g32p_row02_traceSegment_006_0054_0013, g32p_row02_traceSegment_006_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 94 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 81 13 14, g32p_row02_traceSegment_006_0081_0013, g32p_row02_traceSegment_006_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 54 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 54 27 27, g32p_row02_traceSegment_006_0054_0027, g32p_row02_traceSegment_006_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 0 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 54 54, g32p_row02_traceSegment_006_0000_0054, g32p_row02_traceSegment_006_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 108 13 14, g32p_row02_traceSegment_006_0108_0013, g32p_row02_traceSegment_006_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 135 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 135 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 135 13 14, g32p_row02_traceSegment_006_0135_0013, g32p_row02_traceSegment_006_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 108 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 108 27 27, g32p_row02_traceSegment_006_0108_0027, g32p_row02_traceSegment_006_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 162 13 14, g32p_row02_traceSegment_006_0162_0013, g32p_row02_traceSegment_006_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 189 13 14, g32p_row02_traceSegment_006_0189_0013, g32p_row02_traceSegment_006_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 162 27 27, g32p_row02_traceSegment_006_0162_0027, g32p_row02_traceSegment_006_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 108 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 108 54 54, g32p_row02_traceSegment_006_0108_0054, g32p_row02_traceSegment_006_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 0 216 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 108 108, g32p_row02_traceSegment_006_0000_0108, g32p_row02_traceSegment_006_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 216 13 14, g32p_row02_traceSegment_006_0216_0013, g32p_row02_traceSegment_006_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 243 13 14, g32p_row02_traceSegment_006_0243_0013, g32p_row02_traceSegment_006_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 216 27 27, g32p_row02_traceSegment_006_0216_0027, g32p_row02_traceSegment_006_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 270 13 14, g32p_row02_traceSegment_006_0270_0013, g32p_row02_traceSegment_006_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 297 13 14, g32p_row02_traceSegment_006_0297_0013, g32p_row02_traceSegment_006_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 270 27 27, g32p_row02_traceSegment_006_0270_0027, g32p_row02_traceSegment_006_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 216 54 54, g32p_row02_traceSegment_006_0216_0054, g32p_row02_traceSegment_006_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 324 13 14, g32p_row02_traceSegment_006_0324_0013, g32p_row02_traceSegment_006_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 351 13 14, g32p_row02_traceSegment_006_0351_0013, g32p_row02_traceSegment_006_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 324 27 27, g32p_row02_traceSegment_006_0324_0027, g32p_row02_traceSegment_006_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 378 13 14, g32p_row02_traceSegment_006_0378_0013, g32p_row02_traceSegment_006_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 418 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 405 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 405 13 14, g32p_row02_traceSegment_006_0405_0013, g32p_row02_traceSegment_006_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 378 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 378 27 27, g32p_row02_traceSegment_006_0378_0027, g32p_row02_traceSegment_006_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 324 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 324 54 54, g32p_row02_traceSegment_006_0324_0054, g32p_row02_traceSegment_006_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 216 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 216 108 108, g32p_row02_traceSegment_006_0216_0108, g32p_row02_traceSegment_006_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 0 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 216 216, g32p_row02_traceSegment_006_0000_0216, g32p_row02_traceSegment_006_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 445 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 432 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 432 13 14, g32p_row02_traceSegment_006_0432_0013, g32p_row02_traceSegment_006_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 459 13 14, g32p_row02_traceSegment_006_0459_0013, g32p_row02_traceSegment_006_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 432 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 432 27 27, g32p_row02_traceSegment_006_0432_0027, g32p_row02_traceSegment_006_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 486 13 14, g32p_row02_traceSegment_006_0486_0013, g32p_row02_traceSegment_006_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 513 13 14, g32p_row02_traceSegment_006_0513_0013, g32p_row02_traceSegment_006_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 486 27 27, g32p_row02_traceSegment_006_0486_0027, g32p_row02_traceSegment_006_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 432 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 432 54 54, g32p_row02_traceSegment_006_0432_0054, g32p_row02_traceSegment_006_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 540 13 14, g32p_row02_traceSegment_006_0540_0013, g32p_row02_traceSegment_006_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 567 13 14, g32p_row02_traceSegment_006_0567_0013, g32p_row02_traceSegment_006_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 540 27 27, g32p_row02_traceSegment_006_0540_0027, g32p_row02_traceSegment_006_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 594 13 14, g32p_row02_traceSegment_006_0594_0013, g32p_row02_traceSegment_006_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 621 13 14, g32p_row02_traceSegment_006_0621_0013, g32p_row02_traceSegment_006_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 594 27 27, g32p_row02_traceSegment_006_0594_0027, g32p_row02_traceSegment_006_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 540 54 54, g32p_row02_traceSegment_006_0540_0054, g32p_row02_traceSegment_006_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 432 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 432 108 108, g32p_row02_traceSegment_006_0432_0108, g32p_row02_traceSegment_006_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 648 13 14, g32p_row02_traceSegment_006_0648_0013, g32p_row02_traceSegment_006_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 688 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 675 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 675 13 14, g32p_row02_traceSegment_006_0675_0013, g32p_row02_traceSegment_006_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 648 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 648 27 27, g32p_row02_traceSegment_006_0648_0027, g32p_row02_traceSegment_006_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 702 13 14, g32p_row02_traceSegment_006_0702_0013, g32p_row02_traceSegment_006_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 729 13 14, g32p_row02_traceSegment_006_0729_0013, g32p_row02_traceSegment_006_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 702 27 27, g32p_row02_traceSegment_006_0702_0027, g32p_row02_traceSegment_006_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 648 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 648 54 54, g32p_row02_traceSegment_006_0648_0054, g32p_row02_traceSegment_006_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 756 13 14, g32p_row02_traceSegment_006_0756_0013, g32p_row02_traceSegment_006_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 783 13 14, g32p_row02_traceSegment_006_0783_0013, g32p_row02_traceSegment_006_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 756 27 27, g32p_row02_traceSegment_006_0756_0027, g32p_row02_traceSegment_006_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 810 13 14, g32p_row02_traceSegment_006_0810_0013, g32p_row02_traceSegment_006_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 837 13 14, g32p_row02_traceSegment_006_0837_0013, g32p_row02_traceSegment_006_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 810 27 27, g32p_row02_traceSegment_006_0810_0027, g32p_row02_traceSegment_006_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 756 54 54, g32p_row02_traceSegment_006_0756_0054, g32p_row02_traceSegment_006_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 648 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 648 108 108, g32p_row02_traceSegment_006_0648_0108, g32p_row02_traceSegment_006_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 432 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 432 216 216, g32p_row02_traceSegment_006_0432_0216, g32p_row02_traceSegment_006_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_006 0 864 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 432 432, g32p_row02_traceSegment_006_0000_0432, g32p_row02_traceSegment_006_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 864 13 14, g32p_row02_traceSegment_006_0864_0013, g32p_row02_traceSegment_006_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 891 13 14, g32p_row02_traceSegment_006_0891_0013, g32p_row02_traceSegment_006_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 864 27 27, g32p_row02_traceSegment_006_0864_0027, g32p_row02_traceSegment_006_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 918 13 14, g32p_row02_traceSegment_006_0918_0013, g32p_row02_traceSegment_006_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 945 13 14, g32p_row02_traceSegment_006_0945_0013, g32p_row02_traceSegment_006_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 918 27 27, g32p_row02_traceSegment_006_0918_0027, g32p_row02_traceSegment_006_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 864 54 54, g32p_row02_traceSegment_006_0864_0054, g32p_row02_traceSegment_006_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 972 13 14, g32p_row02_traceSegment_006_0972_0013, g32p_row02_traceSegment_006_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 999 13 14, g32p_row02_traceSegment_006_0999_0013, g32p_row02_traceSegment_006_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 972 27 27, g32p_row02_traceSegment_006_0972_0027, g32p_row02_traceSegment_006_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1026 13 14, g32p_row02_traceSegment_006_1026_0013, g32p_row02_traceSegment_006_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1053 13 14, g32p_row02_traceSegment_006_1053_0013, g32p_row02_traceSegment_006_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1026 27 27, g32p_row02_traceSegment_006_1026_0027, g32p_row02_traceSegment_006_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 972 54 54, g32p_row02_traceSegment_006_0972_0054, g32p_row02_traceSegment_006_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 864 108 108, g32p_row02_traceSegment_006_0864_0108, g32p_row02_traceSegment_006_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1080 13 14, g32p_row02_traceSegment_006_1080_0013, g32p_row02_traceSegment_006_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1107 13 14, g32p_row02_traceSegment_006_1107_0013, g32p_row02_traceSegment_006_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1080 27 27, g32p_row02_traceSegment_006_1080_0027, g32p_row02_traceSegment_006_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1134 13 14, g32p_row02_traceSegment_006_1134_0013, g32p_row02_traceSegment_006_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1174 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1161 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1161 13 14, g32p_row02_traceSegment_006_1161_0013, g32p_row02_traceSegment_006_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1134 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1134 27 27, g32p_row02_traceSegment_006_1134_0027, g32p_row02_traceSegment_006_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1080 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1080 54 54, g32p_row02_traceSegment_006_1080_0054, g32p_row02_traceSegment_006_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1201 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1188 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1188 13 14, g32p_row02_traceSegment_006_1188_0013, g32p_row02_traceSegment_006_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1215 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1228 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1215 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1215 13 14, g32p_row02_traceSegment_006_1215_0013, g32p_row02_traceSegment_006_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1188 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1188 27 27, g32p_row02_traceSegment_006_1188_0027, g32p_row02_traceSegment_006_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1242 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1242 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1242 13 14, g32p_row02_traceSegment_006_1242_0013, g32p_row02_traceSegment_006_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1269 13 14, g32p_row02_traceSegment_006_1269_0013, g32p_row02_traceSegment_006_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1242 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1242 27 27, g32p_row02_traceSegment_006_1242_0027, g32p_row02_traceSegment_006_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1188 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1188 54 54, g32p_row02_traceSegment_006_1188_0054, g32p_row02_traceSegment_006_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 1080 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1080 108 108, g32p_row02_traceSegment_006_1080_0108, g32p_row02_traceSegment_006_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 864 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 864 216 216, g32p_row02_traceSegment_006_0864_0216, g32p_row02_traceSegment_006_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1296 13 14, g32p_row02_traceSegment_006_1296_0013, g32p_row02_traceSegment_006_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1323 13 14, g32p_row02_traceSegment_006_1323_0013, g32p_row02_traceSegment_006_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1296 27 27, g32p_row02_traceSegment_006_1296_0027, g32p_row02_traceSegment_006_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1350 13 14, g32p_row02_traceSegment_006_1350_0013, g32p_row02_traceSegment_006_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1377 13 14, g32p_row02_traceSegment_006_1377_0013, g32p_row02_traceSegment_006_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1350 27 27, g32p_row02_traceSegment_006_1350_0027, g32p_row02_traceSegment_006_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1296 54 54, g32p_row02_traceSegment_006_1296_0054, g32p_row02_traceSegment_006_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1404 13 14, g32p_row02_traceSegment_006_1404_0013, g32p_row02_traceSegment_006_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1431 13 14, g32p_row02_traceSegment_006_1431_0013, g32p_row02_traceSegment_006_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1404 27 27, g32p_row02_traceSegment_006_1404_0027, g32p_row02_traceSegment_006_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1458 13 14, g32p_row02_traceSegment_006_1458_0013, g32p_row02_traceSegment_006_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1485 13 14, g32p_row02_traceSegment_006_1485_0013, g32p_row02_traceSegment_006_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1458 27 27, g32p_row02_traceSegment_006_1458_0027, g32p_row02_traceSegment_006_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1404 54 54, g32p_row02_traceSegment_006_1404_0054, g32p_row02_traceSegment_006_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1296 108 108, g32p_row02_traceSegment_006_1296_0108, g32p_row02_traceSegment_006_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1512 13 14, g32p_row02_traceSegment_006_1512_0013, g32p_row02_traceSegment_006_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1539 13 14, g32p_row02_traceSegment_006_1539_0013, g32p_row02_traceSegment_006_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1512 27 27, g32p_row02_traceSegment_006_1512_0027, g32p_row02_traceSegment_006_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1566 13 14, g32p_row02_traceSegment_006_1566_0013, g32p_row02_traceSegment_006_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1593 13 14, g32p_row02_traceSegment_006_1593_0013, g32p_row02_traceSegment_006_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1566 27 27, g32p_row02_traceSegment_006_1566_0027, g32p_row02_traceSegment_006_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1512 54 54, g32p_row02_traceSegment_006_1512_0054, g32p_row02_traceSegment_006_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1620 13 14, g32p_row02_traceSegment_006_1620_0013, g32p_row02_traceSegment_006_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1647 13 14, g32p_row02_traceSegment_006_1647_0013, g32p_row02_traceSegment_006_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1620 27 27, g32p_row02_traceSegment_006_1620_0027, g32p_row02_traceSegment_006_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1674 13 14, g32p_row02_traceSegment_006_1674_0013, g32p_row02_traceSegment_006_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1701 13 14, g32p_row02_traceSegment_006_1701_0013, g32p_row02_traceSegment_006_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1674 27 27, g32p_row02_traceSegment_006_1674_0027, g32p_row02_traceSegment_006_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1620 54 54, g32p_row02_traceSegment_006_1620_0054, g32p_row02_traceSegment_006_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1512 108 108, g32p_row02_traceSegment_006_1512_0108, g32p_row02_traceSegment_006_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1296 216 216, g32p_row02_traceSegment_006_1296_0216, g32p_row02_traceSegment_006_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_006 864 864 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 864 432 432, g32p_row02_traceSegment_006_0864_0432, g32p_row02_traceSegment_006_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_006 0 1728 = [14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 864 864, g32p_row02_traceSegment_006_0000_0864, g32p_row02_traceSegment_006_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1728 13 14, g32p_row02_traceSegment_006_1728_0013, g32p_row02_traceSegment_006_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1755 13 14, g32p_row02_traceSegment_006_1755_0013, g32p_row02_traceSegment_006_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1728 27 27, g32p_row02_traceSegment_006_1728_0027, g32p_row02_traceSegment_006_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1782 13 14, g32p_row02_traceSegment_006_1782_0013, g32p_row02_traceSegment_006_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1809 13 14, g32p_row02_traceSegment_006_1809_0013, g32p_row02_traceSegment_006_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1782 27 27, g32p_row02_traceSegment_006_1782_0027, g32p_row02_traceSegment_006_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1728 54 54, g32p_row02_traceSegment_006_1728_0054, g32p_row02_traceSegment_006_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1836 13 14, g32p_row02_traceSegment_006_1836_0013, g32p_row02_traceSegment_006_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1863 13 14, g32p_row02_traceSegment_006_1863_0013, g32p_row02_traceSegment_006_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1836 27 27, g32p_row02_traceSegment_006_1836_0027, g32p_row02_traceSegment_006_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1890 13 14, g32p_row02_traceSegment_006_1890_0013, g32p_row02_traceSegment_006_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1917 13 14, g32p_row02_traceSegment_006_1917_0013, g32p_row02_traceSegment_006_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1890 27 27, g32p_row02_traceSegment_006_1890_0027, g32p_row02_traceSegment_006_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1836 54 54, g32p_row02_traceSegment_006_1836_0054, g32p_row02_traceSegment_006_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1728 108 108, g32p_row02_traceSegment_006_1728_0108, g32p_row02_traceSegment_006_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1944 13 14, g32p_row02_traceSegment_006_1944_0013, g32p_row02_traceSegment_006_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1971 13 14, g32p_row02_traceSegment_006_1971_0013, g32p_row02_traceSegment_006_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1944 27 27, g32p_row02_traceSegment_006_1944_0027, g32p_row02_traceSegment_006_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1998 13 14, g32p_row02_traceSegment_006_1998_0013, g32p_row02_traceSegment_006_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2025 13 14, g32p_row02_traceSegment_006_2025_0013, g32p_row02_traceSegment_006_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1998 27 27, g32p_row02_traceSegment_006_1998_0027, g32p_row02_traceSegment_006_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1944 54 54, g32p_row02_traceSegment_006_1944_0054, g32p_row02_traceSegment_006_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2052 13 14, g32p_row02_traceSegment_006_2052_0013, g32p_row02_traceSegment_006_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2079 13 14, g32p_row02_traceSegment_006_2079_0013, g32p_row02_traceSegment_006_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2052 27 27, g32p_row02_traceSegment_006_2052_0027, g32p_row02_traceSegment_006_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2106 13 14, g32p_row02_traceSegment_006_2106_0013, g32p_row02_traceSegment_006_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2133 13 14, g32p_row02_traceSegment_006_2133_0013, g32p_row02_traceSegment_006_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2106 27 27, g32p_row02_traceSegment_006_2106_0027, g32p_row02_traceSegment_006_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2052 54 54, g32p_row02_traceSegment_006_2052_0054, g32p_row02_traceSegment_006_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1944 108 108, g32p_row02_traceSegment_006_1944_0108, g32p_row02_traceSegment_006_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1728 216 216, g32p_row02_traceSegment_006_1728_0216, g32p_row02_traceSegment_006_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2160 13 14, g32p_row02_traceSegment_006_2160_0013, g32p_row02_traceSegment_006_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2187 13 14, g32p_row02_traceSegment_006_2187_0013, g32p_row02_traceSegment_006_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2160 27 27, g32p_row02_traceSegment_006_2160_0027, g32p_row02_traceSegment_006_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2214 13 14, g32p_row02_traceSegment_006_2214_0013, g32p_row02_traceSegment_006_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2241 13 14, g32p_row02_traceSegment_006_2241_0013, g32p_row02_traceSegment_006_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2214 27 27, g32p_row02_traceSegment_006_2214_0027, g32p_row02_traceSegment_006_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2160 54 54, g32p_row02_traceSegment_006_2160_0054, g32p_row02_traceSegment_006_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2268 13 14, g32p_row02_traceSegment_006_2268_0013, g32p_row02_traceSegment_006_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2295 13 14, g32p_row02_traceSegment_006_2295_0013, g32p_row02_traceSegment_006_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2268 27 27, g32p_row02_traceSegment_006_2268_0027, g32p_row02_traceSegment_006_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2322 13 14, g32p_row02_traceSegment_006_2322_0013, g32p_row02_traceSegment_006_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2349 13 14, g32p_row02_traceSegment_006_2349_0013, g32p_row02_traceSegment_006_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2322 27 27, g32p_row02_traceSegment_006_2322_0027, g32p_row02_traceSegment_006_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2268 54 54, g32p_row02_traceSegment_006_2268_0054, g32p_row02_traceSegment_006_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2160 108 108, g32p_row02_traceSegment_006_2160_0108, g32p_row02_traceSegment_006_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2376 13 14, g32p_row02_traceSegment_006_2376_0013, g32p_row02_traceSegment_006_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2403 13 14, g32p_row02_traceSegment_006_2403_0013, g32p_row02_traceSegment_006_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2376 27 27, g32p_row02_traceSegment_006_2376_0027, g32p_row02_traceSegment_006_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2430 13 14, g32p_row02_traceSegment_006_2430_0013, g32p_row02_traceSegment_006_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2470 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2457 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2457 13 14, g32p_row02_traceSegment_006_2457_0013, g32p_row02_traceSegment_006_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2430 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2430 27 27, g32p_row02_traceSegment_006_2430_0027, g32p_row02_traceSegment_006_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2376 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2376 54 54, g32p_row02_traceSegment_006_2376_0054, g32p_row02_traceSegment_006_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2484 13 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2484 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2484 13 14, g32p_row02_traceSegment_006_2484_0013, g32p_row02_traceSegment_006_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2524 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2511 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2511 13 14, g32p_row02_traceSegment_006_2511_0013, g32p_row02_traceSegment_006_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2484 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2484 27 27, g32p_row02_traceSegment_006_2484_0027, g32p_row02_traceSegment_006_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2538 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2551 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2538 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2538 13 14, g32p_row02_traceSegment_006_2538_0013, g32p_row02_traceSegment_006_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2578 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2565 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2565 13 14, g32p_row02_traceSegment_006_2565_0013, g32p_row02_traceSegment_006_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2538 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2538 27 27, g32p_row02_traceSegment_006_2538_0027, g32p_row02_traceSegment_006_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2484 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2484 54 54, g32p_row02_traceSegment_006_2484_0054, g32p_row02_traceSegment_006_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 2376 216 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2376 108 108, g32p_row02_traceSegment_006_2376_0108, g32p_row02_traceSegment_006_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 2160 432 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2160 216 216, g32p_row02_traceSegment_006_2160_0216, g32p_row02_traceSegment_006_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 864 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1728 432 432, g32p_row02_traceSegment_006_1728_0432, g32p_row02_traceSegment_006_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2592 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2592 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2592 13 14, g32p_row02_traceSegment_006_2592_0013, g32p_row02_traceSegment_006_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2619 13 14, g32p_row02_traceSegment_006_2619_0013, g32p_row02_traceSegment_006_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2592 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2592 27 27, g32p_row02_traceSegment_006_2592_0027, g32p_row02_traceSegment_006_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2646 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2646 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2646 13 14, g32p_row02_traceSegment_006_2646_0013, g32p_row02_traceSegment_006_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2673 13 14, g32p_row02_traceSegment_006_2673_0013, g32p_row02_traceSegment_006_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2646 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2646 27 27, g32p_row02_traceSegment_006_2646_0027, g32p_row02_traceSegment_006_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2592 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2592 54 54, g32p_row02_traceSegment_006_2592_0054, g32p_row02_traceSegment_006_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2700 13 14, g32p_row02_traceSegment_006_2700_0013, g32p_row02_traceSegment_006_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2727 13 14, g32p_row02_traceSegment_006_2727_0013, g32p_row02_traceSegment_006_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2700 27 27, g32p_row02_traceSegment_006_2700_0027, g32p_row02_traceSegment_006_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2754 13 14, g32p_row02_traceSegment_006_2754_0013, g32p_row02_traceSegment_006_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2781 13 14, g32p_row02_traceSegment_006_2781_0013, g32p_row02_traceSegment_006_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2754 27 27, g32p_row02_traceSegment_006_2754_0027, g32p_row02_traceSegment_006_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2700 54 54, g32p_row02_traceSegment_006_2700_0054, g32p_row02_traceSegment_006_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 2592 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2592 108 108, g32p_row02_traceSegment_006_2592_0108, g32p_row02_traceSegment_006_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2808 13 14, g32p_row02_traceSegment_006_2808_0013, g32p_row02_traceSegment_006_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2848 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2835 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2835 13 14, g32p_row02_traceSegment_006_2835_0013, g32p_row02_traceSegment_006_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2808 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2808 27 27, g32p_row02_traceSegment_006_2808_0027, g32p_row02_traceSegment_006_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2875 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2862 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2862 13 14, g32p_row02_traceSegment_006_2862_0013, g32p_row02_traceSegment_006_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2889 13 14, g32p_row02_traceSegment_006_2889_0013, g32p_row02_traceSegment_006_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2862 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2862 27 27, g32p_row02_traceSegment_006_2862_0027, g32p_row02_traceSegment_006_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2808 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2808 54 54, g32p_row02_traceSegment_006_2808_0054, g32p_row02_traceSegment_006_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2929 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2916 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2916 13 14, g32p_row02_traceSegment_006_2916_0013, g32p_row02_traceSegment_006_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2956 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2943 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2943 13 14, g32p_row02_traceSegment_006_2943_0013, g32p_row02_traceSegment_006_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2916 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2916 27 27, g32p_row02_traceSegment_006_2916_0027, g32p_row02_traceSegment_006_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2970 13 14, g32p_row02_traceSegment_006_2970_0013, g32p_row02_traceSegment_006_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2997 13 14, g32p_row02_traceSegment_006_2997_0013, g32p_row02_traceSegment_006_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2970 27 27, g32p_row02_traceSegment_006_2970_0027, g32p_row02_traceSegment_006_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 2916 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2916 54 54, g32p_row02_traceSegment_006_2916_0054, g32p_row02_traceSegment_006_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 2808 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2808 108 108, g32p_row02_traceSegment_006_2808_0108, g32p_row02_traceSegment_006_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 2592 432 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2592 216 216, g32p_row02_traceSegment_006_2592_0216, g32p_row02_traceSegment_006_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3024 13 14, g32p_row02_traceSegment_006_3024_0013, g32p_row02_traceSegment_006_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3051 13 14, g32p_row02_traceSegment_006_3051_0013, g32p_row02_traceSegment_006_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3024 27 27, g32p_row02_traceSegment_006_3024_0027, g32p_row02_traceSegment_006_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3078 13 14, g32p_row02_traceSegment_006_3078_0013, g32p_row02_traceSegment_006_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3105 13 14, g32p_row02_traceSegment_006_3105_0013, g32p_row02_traceSegment_006_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3078 27 27, g32p_row02_traceSegment_006_3078_0027, g32p_row02_traceSegment_006_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3024 54 54, g32p_row02_traceSegment_006_3024_0054, g32p_row02_traceSegment_006_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3132 13 14, g32p_row02_traceSegment_006_3132_0013, g32p_row02_traceSegment_006_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3159 13 14, g32p_row02_traceSegment_006_3159_0013, g32p_row02_traceSegment_006_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3132 27 27, g32p_row02_traceSegment_006_3132_0027, g32p_row02_traceSegment_006_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3186 13 14, g32p_row02_traceSegment_006_3186_0013, g32p_row02_traceSegment_006_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3213 13 14, g32p_row02_traceSegment_006_3213_0013, g32p_row02_traceSegment_006_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3186 27 27, g32p_row02_traceSegment_006_3186_0027, g32p_row02_traceSegment_006_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3132 54 54, g32p_row02_traceSegment_006_3132_0054, g32p_row02_traceSegment_006_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3024 108 108, g32p_row02_traceSegment_006_3024_0108, g32p_row02_traceSegment_006_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3240 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3253 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3240 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3240 13 14, g32p_row02_traceSegment_006_3240_0013, g32p_row02_traceSegment_006_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3267 13 14, g32p_row02_traceSegment_006_3267_0013, g32p_row02_traceSegment_006_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3240 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3240 27 27, g32p_row02_traceSegment_006_3240_0027, g32p_row02_traceSegment_006_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3294 13 14, g32p_row02_traceSegment_006_3294_0013, g32p_row02_traceSegment_006_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3321 13 14, g32p_row02_traceSegment_006_3321_0013, g32p_row02_traceSegment_006_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3294 27 27, g32p_row02_traceSegment_006_3294_0027, g32p_row02_traceSegment_006_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 3240 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3240 54 54, g32p_row02_traceSegment_006_3240_0054, g32p_row02_traceSegment_006_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3348 13 14, g32p_row02_traceSegment_006_3348_0013, g32p_row02_traceSegment_006_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3375 13 14, g32p_row02_traceSegment_006_3375_0013, g32p_row02_traceSegment_006_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3348 27 27, g32p_row02_traceSegment_006_3348_0027, g32p_row02_traceSegment_006_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3402 13 14, g32p_row02_traceSegment_006_3402_0013, g32p_row02_traceSegment_006_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_006 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_006 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_006_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_006 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3429 13 14, g32p_row02_traceSegment_006_3429_0013, g32p_row02_traceSegment_006_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_006 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3402 27 27, g32p_row02_traceSegment_006_3402_0027, g32p_row02_traceSegment_006_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_006 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3348 54 54, g32p_row02_traceSegment_006_3348_0054, g32p_row02_traceSegment_006_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_006 3240 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3240 108 108, g32p_row02_traceSegment_006_3240_0108, g32p_row02_traceSegment_006_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_006_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_006 3024 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 3024 216 216, g32p_row02_traceSegment_006_3024_0216, g32p_row02_traceSegment_006_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_006_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_006 2592 864 = [9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 2592 432 432, g32p_row02_traceSegment_006_2592_0432, g32p_row02_traceSegment_006_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_006_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_006 1728 1728 = [18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 1728 864 864, g32p_row02_traceSegment_006_1728_0864, g32p_row02_traceSegment_006_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_006_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_006 0 3456 = [32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_006 0 1728 1728, g32p_row02_traceSegment_006_0000_1728, g32p_row02_traceSegment_006_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_006 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 6 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_006_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_007 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 7 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_007_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 13 14, g32p_row02_traceSegment_007_0000_0013, g32p_row02_traceSegment_007_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 27 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 27 13 14, g32p_row02_traceSegment_007_0027_0013, g32p_row02_traceSegment_007_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 27 27, g32p_row02_traceSegment_007_0000_0027, g32p_row02_traceSegment_007_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 54 13 = [0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 54 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 54 13 14, g32p_row02_traceSegment_007_0054_0013, g32p_row02_traceSegment_007_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 94 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 81 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 81 13 14, g32p_row02_traceSegment_007_0081_0013, g32p_row02_traceSegment_007_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 54 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 54 27 27, g32p_row02_traceSegment_007_0054_0027, g32p_row02_traceSegment_007_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 0 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 54 54, g32p_row02_traceSegment_007_0000_0054, g32p_row02_traceSegment_007_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 108 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 108 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 108 13 14, g32p_row02_traceSegment_007_0108_0013, g32p_row02_traceSegment_007_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 135 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 135 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 135 13 14, g32p_row02_traceSegment_007_0135_0013, g32p_row02_traceSegment_007_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 108 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 108 27 27, g32p_row02_traceSegment_007_0108_0027, g32p_row02_traceSegment_007_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 162 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 162 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 162 13 14, g32p_row02_traceSegment_007_0162_0013, g32p_row02_traceSegment_007_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 189 13 14, g32p_row02_traceSegment_007_0189_0013, g32p_row02_traceSegment_007_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 162 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 162 27 27, g32p_row02_traceSegment_007_0162_0027, g32p_row02_traceSegment_007_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 108 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 108 54 54, g32p_row02_traceSegment_007_0108_0054, g32p_row02_traceSegment_007_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 0 216 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 108 108, g32p_row02_traceSegment_007_0000_0108, g32p_row02_traceSegment_007_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 216 13 14, g32p_row02_traceSegment_007_0216_0013, g32p_row02_traceSegment_007_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 243 13 14, g32p_row02_traceSegment_007_0243_0013, g32p_row02_traceSegment_007_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 216 27 27, g32p_row02_traceSegment_007_0216_0027, g32p_row02_traceSegment_007_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 270 13 14, g32p_row02_traceSegment_007_0270_0013, g32p_row02_traceSegment_007_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 297 13 14, g32p_row02_traceSegment_007_0297_0013, g32p_row02_traceSegment_007_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 270 27 27, g32p_row02_traceSegment_007_0270_0027, g32p_row02_traceSegment_007_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 216 54 54, g32p_row02_traceSegment_007_0216_0054, g32p_row02_traceSegment_007_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 324 13 14, g32p_row02_traceSegment_007_0324_0013, g32p_row02_traceSegment_007_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 351 13 14, g32p_row02_traceSegment_007_0351_0013, g32p_row02_traceSegment_007_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 324 27 27, g32p_row02_traceSegment_007_0324_0027, g32p_row02_traceSegment_007_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 378 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 378 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 378 13 14, g32p_row02_traceSegment_007_0378_0013, g32p_row02_traceSegment_007_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 418 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 405 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 405 13 14, g32p_row02_traceSegment_007_0405_0013, g32p_row02_traceSegment_007_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 378 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 378 27 27, g32p_row02_traceSegment_007_0378_0027, g32p_row02_traceSegment_007_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 324 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 324 54 54, g32p_row02_traceSegment_007_0324_0054, g32p_row02_traceSegment_007_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 216 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 216 108 108, g32p_row02_traceSegment_007_0216_0108, g32p_row02_traceSegment_007_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 0 432 = [0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 216 216, g32p_row02_traceSegment_007_0000_0216, g32p_row02_traceSegment_007_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 432 13 14, g32p_row02_traceSegment_007_0432_0013, g32p_row02_traceSegment_007_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 459 13 14, g32p_row02_traceSegment_007_0459_0013, g32p_row02_traceSegment_007_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 432 27 27, g32p_row02_traceSegment_007_0432_0027, g32p_row02_traceSegment_007_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 486 13 14, g32p_row02_traceSegment_007_0486_0013, g32p_row02_traceSegment_007_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 526 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 513 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 513 13 14, g32p_row02_traceSegment_007_0513_0013, g32p_row02_traceSegment_007_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 486 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 486 27 27, g32p_row02_traceSegment_007_0486_0027, g32p_row02_traceSegment_007_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 432 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 432 54 54, g32p_row02_traceSegment_007_0432_0054, g32p_row02_traceSegment_007_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 540 13 14, g32p_row02_traceSegment_007_0540_0013, g32p_row02_traceSegment_007_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 580 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 567 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 567 13 14, g32p_row02_traceSegment_007_0567_0013, g32p_row02_traceSegment_007_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 540 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 540 27 27, g32p_row02_traceSegment_007_0540_0027, g32p_row02_traceSegment_007_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 594 13 14, g32p_row02_traceSegment_007_0594_0013, g32p_row02_traceSegment_007_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 621 13 14, g32p_row02_traceSegment_007_0621_0013, g32p_row02_traceSegment_007_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 594 27 27, g32p_row02_traceSegment_007_0594_0027, g32p_row02_traceSegment_007_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 540 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 540 54 54, g32p_row02_traceSegment_007_0540_0054, g32p_row02_traceSegment_007_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 432 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 432 108 108, g32p_row02_traceSegment_007_0432_0108, g32p_row02_traceSegment_007_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 648 13 14, g32p_row02_traceSegment_007_0648_0013, g32p_row02_traceSegment_007_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 675 13 14, g32p_row02_traceSegment_007_0675_0013, g32p_row02_traceSegment_007_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 648 27 27, g32p_row02_traceSegment_007_0648_0027, g32p_row02_traceSegment_007_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 715 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 702 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 702 13 14, g32p_row02_traceSegment_007_0702_0013, g32p_row02_traceSegment_007_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 729 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 729 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 729 13 14, g32p_row02_traceSegment_007_0729_0013, g32p_row02_traceSegment_007_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 702 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 702 27 27, g32p_row02_traceSegment_007_0702_0027, g32p_row02_traceSegment_007_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 648 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 648 54 54, g32p_row02_traceSegment_007_0648_0054, g32p_row02_traceSegment_007_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 756 13 14, g32p_row02_traceSegment_007_0756_0013, g32p_row02_traceSegment_007_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 783 13 14, g32p_row02_traceSegment_007_0783_0013, g32p_row02_traceSegment_007_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 756 27 27, g32p_row02_traceSegment_007_0756_0027, g32p_row02_traceSegment_007_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 810 13 14, g32p_row02_traceSegment_007_0810_0013, g32p_row02_traceSegment_007_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 837 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 837 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 837 13 14, g32p_row02_traceSegment_007_0837_0013, g32p_row02_traceSegment_007_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 810 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 810 27 27, g32p_row02_traceSegment_007_0810_0027, g32p_row02_traceSegment_007_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 756 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 756 54 54, g32p_row02_traceSegment_007_0756_0054, g32p_row02_traceSegment_007_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 648 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 648 108 108, g32p_row02_traceSegment_007_0648_0108, g32p_row02_traceSegment_007_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 432 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 432 216 216, g32p_row02_traceSegment_007_0432_0216, g32p_row02_traceSegment_007_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_007 0 864 = [0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 432 432, g32p_row02_traceSegment_007_0000_0432, g32p_row02_traceSegment_007_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 864 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 864 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 864 13 14, g32p_row02_traceSegment_007_0864_0013, g32p_row02_traceSegment_007_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 891 13 14, g32p_row02_traceSegment_007_0891_0013, g32p_row02_traceSegment_007_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 864 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 864 27 27, g32p_row02_traceSegment_007_0864_0027, g32p_row02_traceSegment_007_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 918 13 14, g32p_row02_traceSegment_007_0918_0013, g32p_row02_traceSegment_007_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 945 13 14, g32p_row02_traceSegment_007_0945_0013, g32p_row02_traceSegment_007_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 918 27 27, g32p_row02_traceSegment_007_0918_0027, g32p_row02_traceSegment_007_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 864 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 864 54 54, g32p_row02_traceSegment_007_0864_0054, g32p_row02_traceSegment_007_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 972 13 14, g32p_row02_traceSegment_007_0972_0013, g32p_row02_traceSegment_007_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 999 13 14, g32p_row02_traceSegment_007_0999_0013, g32p_row02_traceSegment_007_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 972 27 27, g32p_row02_traceSegment_007_0972_0027, g32p_row02_traceSegment_007_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1026 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1026 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1026 13 14, g32p_row02_traceSegment_007_1026_0013, g32p_row02_traceSegment_007_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1053 13 14, g32p_row02_traceSegment_007_1053_0013, g32p_row02_traceSegment_007_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1026 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1026 27 27, g32p_row02_traceSegment_007_1026_0027, g32p_row02_traceSegment_007_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 972 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 972 54 54, g32p_row02_traceSegment_007_0972_0054, g32p_row02_traceSegment_007_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 864 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 864 108 108, g32p_row02_traceSegment_007_0864_0108, g32p_row02_traceSegment_007_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1080 13 14, g32p_row02_traceSegment_007_1080_0013, g32p_row02_traceSegment_007_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1107 13 14, g32p_row02_traceSegment_007_1107_0013, g32p_row02_traceSegment_007_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1080 27 27, g32p_row02_traceSegment_007_1080_0027, g32p_row02_traceSegment_007_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1134 13 14, g32p_row02_traceSegment_007_1134_0013, g32p_row02_traceSegment_007_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1161 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1161 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1161 13 14, g32p_row02_traceSegment_007_1161_0013, g32p_row02_traceSegment_007_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1134 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1134 27 27, g32p_row02_traceSegment_007_1134_0027, g32p_row02_traceSegment_007_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1080 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1080 54 54, g32p_row02_traceSegment_007_1080_0054, g32p_row02_traceSegment_007_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1188 13 14, g32p_row02_traceSegment_007_1188_0013, g32p_row02_traceSegment_007_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1215 13 14, g32p_row02_traceSegment_007_1215_0013, g32p_row02_traceSegment_007_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1188 27 27, g32p_row02_traceSegment_007_1188_0027, g32p_row02_traceSegment_007_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1242 13 14, g32p_row02_traceSegment_007_1242_0013, g32p_row02_traceSegment_007_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1269 13 14, g32p_row02_traceSegment_007_1269_0013, g32p_row02_traceSegment_007_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1242 27 27, g32p_row02_traceSegment_007_1242_0027, g32p_row02_traceSegment_007_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1188 54 54, g32p_row02_traceSegment_007_1188_0054, g32p_row02_traceSegment_007_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 1080 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1080 108 108, g32p_row02_traceSegment_007_1080_0108, g32p_row02_traceSegment_007_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 864 432 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 864 216 216, g32p_row02_traceSegment_007_0864_0216, g32p_row02_traceSegment_007_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1296 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1296 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1296 13 14, g32p_row02_traceSegment_007_1296_0013, g32p_row02_traceSegment_007_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1323 13 14, g32p_row02_traceSegment_007_1323_0013, g32p_row02_traceSegment_007_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1296 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1296 27 27, g32p_row02_traceSegment_007_1296_0027, g32p_row02_traceSegment_007_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1350 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1363 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1350 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1350 13 14, g32p_row02_traceSegment_007_1350_0013, g32p_row02_traceSegment_007_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1377 13 14, g32p_row02_traceSegment_007_1377_0013, g32p_row02_traceSegment_007_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1350 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1350 27 27, g32p_row02_traceSegment_007_1350_0027, g32p_row02_traceSegment_007_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1296 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1296 54 54, g32p_row02_traceSegment_007_1296_0054, g32p_row02_traceSegment_007_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1404 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1404 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1404 13 14, g32p_row02_traceSegment_007_1404_0013, g32p_row02_traceSegment_007_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1431 13 14, g32p_row02_traceSegment_007_1431_0013, g32p_row02_traceSegment_007_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1404 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1404 27 27, g32p_row02_traceSegment_007_1404_0027, g32p_row02_traceSegment_007_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1458 13 14, g32p_row02_traceSegment_007_1458_0013, g32p_row02_traceSegment_007_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1498 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1485 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1485 13 14, g32p_row02_traceSegment_007_1485_0013, g32p_row02_traceSegment_007_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1458 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1458 27 27, g32p_row02_traceSegment_007_1458_0027, g32p_row02_traceSegment_007_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1404 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1404 54 54, g32p_row02_traceSegment_007_1404_0054, g32p_row02_traceSegment_007_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 1296 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1296 108 108, g32p_row02_traceSegment_007_1296_0108, g32p_row02_traceSegment_007_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1512 13 14, g32p_row02_traceSegment_007_1512_0013, g32p_row02_traceSegment_007_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1539 13 14, g32p_row02_traceSegment_007_1539_0013, g32p_row02_traceSegment_007_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1512 27 27, g32p_row02_traceSegment_007_1512_0027, g32p_row02_traceSegment_007_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1566 13 14, g32p_row02_traceSegment_007_1566_0013, g32p_row02_traceSegment_007_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1593 13 14, g32p_row02_traceSegment_007_1593_0013, g32p_row02_traceSegment_007_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1566 27 27, g32p_row02_traceSegment_007_1566_0027, g32p_row02_traceSegment_007_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1512 54 54, g32p_row02_traceSegment_007_1512_0054, g32p_row02_traceSegment_007_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1620 13 14, g32p_row02_traceSegment_007_1620_0013, g32p_row02_traceSegment_007_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1647 13 14, g32p_row02_traceSegment_007_1647_0013, g32p_row02_traceSegment_007_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1620 27 27, g32p_row02_traceSegment_007_1620_0027, g32p_row02_traceSegment_007_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1674 13 14, g32p_row02_traceSegment_007_1674_0013, g32p_row02_traceSegment_007_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1701 13 14, g32p_row02_traceSegment_007_1701_0013, g32p_row02_traceSegment_007_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1674 27 27, g32p_row02_traceSegment_007_1674_0027, g32p_row02_traceSegment_007_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1620 54 54, g32p_row02_traceSegment_007_1620_0054, g32p_row02_traceSegment_007_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1512 108 108, g32p_row02_traceSegment_007_1512_0108, g32p_row02_traceSegment_007_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 1296 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1296 216 216, g32p_row02_traceSegment_007_1296_0216, g32p_row02_traceSegment_007_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_007 864 864 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 864 432 432, g32p_row02_traceSegment_007_0864_0432, g32p_row02_traceSegment_007_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_007 0 1728 = [0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 864 864, g32p_row02_traceSegment_007_0000_0864, g32p_row02_traceSegment_007_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1728 13 14, g32p_row02_traceSegment_007_1728_0013, g32p_row02_traceSegment_007_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1755 13 14, g32p_row02_traceSegment_007_1755_0013, g32p_row02_traceSegment_007_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1728 27 27, g32p_row02_traceSegment_007_1728_0027, g32p_row02_traceSegment_007_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1795 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1782 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1782 13 14, g32p_row02_traceSegment_007_1782_0013, g32p_row02_traceSegment_007_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1809 13 14, g32p_row02_traceSegment_007_1809_0013, g32p_row02_traceSegment_007_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1782 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1782 27 27, g32p_row02_traceSegment_007_1782_0027, g32p_row02_traceSegment_007_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1728 54 54, g32p_row02_traceSegment_007_1728_0054, g32p_row02_traceSegment_007_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1849 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1836 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1836 13 14, g32p_row02_traceSegment_007_1836_0013, g32p_row02_traceSegment_007_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1863 13 14, g32p_row02_traceSegment_007_1863_0013, g32p_row02_traceSegment_007_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1836 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1836 27 27, g32p_row02_traceSegment_007_1836_0027, g32p_row02_traceSegment_007_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1890 13 14, g32p_row02_traceSegment_007_1890_0013, g32p_row02_traceSegment_007_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1917 13 14, g32p_row02_traceSegment_007_1917_0013, g32p_row02_traceSegment_007_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1890 27 27, g32p_row02_traceSegment_007_1890_0027, g32p_row02_traceSegment_007_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1836 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1836 54 54, g32p_row02_traceSegment_007_1836_0054, g32p_row02_traceSegment_007_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1728 108 108, g32p_row02_traceSegment_007_1728_0108, g32p_row02_traceSegment_007_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1944 13 14, g32p_row02_traceSegment_007_1944_0013, g32p_row02_traceSegment_007_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1971 13 14, g32p_row02_traceSegment_007_1971_0013, g32p_row02_traceSegment_007_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1944 27 27, g32p_row02_traceSegment_007_1944_0027, g32p_row02_traceSegment_007_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1998 13 14, g32p_row02_traceSegment_007_1998_0013, g32p_row02_traceSegment_007_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2025 13 14, g32p_row02_traceSegment_007_2025_0013, g32p_row02_traceSegment_007_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1998 27 27, g32p_row02_traceSegment_007_1998_0027, g32p_row02_traceSegment_007_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1944 54 54, g32p_row02_traceSegment_007_1944_0054, g32p_row02_traceSegment_007_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2052 13 14, g32p_row02_traceSegment_007_2052_0013, g32p_row02_traceSegment_007_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2079 13 14, g32p_row02_traceSegment_007_2079_0013, g32p_row02_traceSegment_007_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2052 27 27, g32p_row02_traceSegment_007_2052_0027, g32p_row02_traceSegment_007_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2106 13 14, g32p_row02_traceSegment_007_2106_0013, g32p_row02_traceSegment_007_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2133 13 14, g32p_row02_traceSegment_007_2133_0013, g32p_row02_traceSegment_007_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2106 27 27, g32p_row02_traceSegment_007_2106_0027, g32p_row02_traceSegment_007_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2052 54 54, g32p_row02_traceSegment_007_2052_0054, g32p_row02_traceSegment_007_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1944 108 108, g32p_row02_traceSegment_007_1944_0108, g32p_row02_traceSegment_007_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1728 216 216, g32p_row02_traceSegment_007_1728_0216, g32p_row02_traceSegment_007_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2160 13 14, g32p_row02_traceSegment_007_2160_0013, g32p_row02_traceSegment_007_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2187 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2187 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2187 13 14, g32p_row02_traceSegment_007_2187_0013, g32p_row02_traceSegment_007_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2160 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2160 27 27, g32p_row02_traceSegment_007_2160_0027, g32p_row02_traceSegment_007_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2214 13 14, g32p_row02_traceSegment_007_2214_0013, g32p_row02_traceSegment_007_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2241 13 14, g32p_row02_traceSegment_007_2241_0013, g32p_row02_traceSegment_007_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2214 27 27, g32p_row02_traceSegment_007_2214_0027, g32p_row02_traceSegment_007_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2160 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2160 54 54, g32p_row02_traceSegment_007_2160_0054, g32p_row02_traceSegment_007_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2281 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2268 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2268 13 14, g32p_row02_traceSegment_007_2268_0013, g32p_row02_traceSegment_007_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2295 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2295 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2295 13 14, g32p_row02_traceSegment_007_2295_0013, g32p_row02_traceSegment_007_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2268 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2268 27 27, g32p_row02_traceSegment_007_2268_0027, g32p_row02_traceSegment_007_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2322 13 14, g32p_row02_traceSegment_007_2322_0013, g32p_row02_traceSegment_007_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2349 13 14, g32p_row02_traceSegment_007_2349_0013, g32p_row02_traceSegment_007_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2322 27 27, g32p_row02_traceSegment_007_2322_0027, g32p_row02_traceSegment_007_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2268 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2268 54 54, g32p_row02_traceSegment_007_2268_0054, g32p_row02_traceSegment_007_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 2160 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2160 108 108, g32p_row02_traceSegment_007_2160_0108, g32p_row02_traceSegment_007_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2376 13 14, g32p_row02_traceSegment_007_2376_0013, g32p_row02_traceSegment_007_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2403 13 14, g32p_row02_traceSegment_007_2403_0013, g32p_row02_traceSegment_007_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2376 27 27, g32p_row02_traceSegment_007_2376_0027, g32p_row02_traceSegment_007_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2430 13 14, g32p_row02_traceSegment_007_2430_0013, g32p_row02_traceSegment_007_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2470 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2457 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2457 13 14, g32p_row02_traceSegment_007_2457_0013, g32p_row02_traceSegment_007_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2430 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2430 27 27, g32p_row02_traceSegment_007_2430_0027, g32p_row02_traceSegment_007_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2376 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2376 54 54, g32p_row02_traceSegment_007_2376_0054, g32p_row02_traceSegment_007_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2484 13 14, g32p_row02_traceSegment_007_2484_0013, g32p_row02_traceSegment_007_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2511 13 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2511 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2511 13 14, g32p_row02_traceSegment_007_2511_0013, g32p_row02_traceSegment_007_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2484 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2484 27 27, g32p_row02_traceSegment_007_2484_0027, g32p_row02_traceSegment_007_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2538 13 14, g32p_row02_traceSegment_007_2538_0013, g32p_row02_traceSegment_007_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2565 13 14, g32p_row02_traceSegment_007_2565_0013, g32p_row02_traceSegment_007_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2538 27 27, g32p_row02_traceSegment_007_2538_0027, g32p_row02_traceSegment_007_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2484 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2484 54 54, g32p_row02_traceSegment_007_2484_0054, g32p_row02_traceSegment_007_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 2376 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2376 108 108, g32p_row02_traceSegment_007_2376_0108, g32p_row02_traceSegment_007_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 2160 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2160 216 216, g32p_row02_traceSegment_007_2160_0216, g32p_row02_traceSegment_007_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 864 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1728 432 432, g32p_row02_traceSegment_007_1728_0432, g32p_row02_traceSegment_007_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2592 13 14, g32p_row02_traceSegment_007_2592_0013, g32p_row02_traceSegment_007_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2619 13 14, g32p_row02_traceSegment_007_2619_0013, g32p_row02_traceSegment_007_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2592 27 27, g32p_row02_traceSegment_007_2592_0027, g32p_row02_traceSegment_007_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2646 13 14, g32p_row02_traceSegment_007_2646_0013, g32p_row02_traceSegment_007_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2673 13 14, g32p_row02_traceSegment_007_2673_0013, g32p_row02_traceSegment_007_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2646 27 27, g32p_row02_traceSegment_007_2646_0027, g32p_row02_traceSegment_007_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2592 54 54, g32p_row02_traceSegment_007_2592_0054, g32p_row02_traceSegment_007_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2713 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2700 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2700 13 14, g32p_row02_traceSegment_007_2700_0013, g32p_row02_traceSegment_007_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2727 13 14, g32p_row02_traceSegment_007_2727_0013, g32p_row02_traceSegment_007_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2700 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2700 27 27, g32p_row02_traceSegment_007_2700_0027, g32p_row02_traceSegment_007_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2754 13 14, g32p_row02_traceSegment_007_2754_0013, g32p_row02_traceSegment_007_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2781 13 14, g32p_row02_traceSegment_007_2781_0013, g32p_row02_traceSegment_007_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2754 27 27, g32p_row02_traceSegment_007_2754_0027, g32p_row02_traceSegment_007_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2700 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2700 54 54, g32p_row02_traceSegment_007_2700_0054, g32p_row02_traceSegment_007_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 2592 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2592 108 108, g32p_row02_traceSegment_007_2592_0108, g32p_row02_traceSegment_007_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2808 13 14, g32p_row02_traceSegment_007_2808_0013, g32p_row02_traceSegment_007_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2835 13 14, g32p_row02_traceSegment_007_2835_0013, g32p_row02_traceSegment_007_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2808 27 27, g32p_row02_traceSegment_007_2808_0027, g32p_row02_traceSegment_007_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2862 13 14, g32p_row02_traceSegment_007_2862_0013, g32p_row02_traceSegment_007_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2889 13 14, g32p_row02_traceSegment_007_2889_0013, g32p_row02_traceSegment_007_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2862 27 27, g32p_row02_traceSegment_007_2862_0027, g32p_row02_traceSegment_007_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2808 54 54, g32p_row02_traceSegment_007_2808_0054, g32p_row02_traceSegment_007_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2916 13 14, g32p_row02_traceSegment_007_2916_0013, g32p_row02_traceSegment_007_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2943 13 14, g32p_row02_traceSegment_007_2943_0013, g32p_row02_traceSegment_007_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2916 27 27, g32p_row02_traceSegment_007_2916_0027, g32p_row02_traceSegment_007_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2970 13 14, g32p_row02_traceSegment_007_2970_0013, g32p_row02_traceSegment_007_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 2997 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3010 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 2997 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2997 13 14, g32p_row02_traceSegment_007_2997_0013, g32p_row02_traceSegment_007_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 2970 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2970 27 27, g32p_row02_traceSegment_007_2970_0027, g32p_row02_traceSegment_007_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 2916 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2916 54 54, g32p_row02_traceSegment_007_2916_0054, g32p_row02_traceSegment_007_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 2808 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2808 108 108, g32p_row02_traceSegment_007_2808_0108, g32p_row02_traceSegment_007_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 2592 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2592 216 216, g32p_row02_traceSegment_007_2592_0216, g32p_row02_traceSegment_007_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3037 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3024 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3024 13 14, g32p_row02_traceSegment_007_3024_0013, g32p_row02_traceSegment_007_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3064 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3051 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3051 13 14, g32p_row02_traceSegment_007_3051_0013, g32p_row02_traceSegment_007_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3024 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3024 27 27, g32p_row02_traceSegment_007_3024_0027, g32p_row02_traceSegment_007_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3078 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3078 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3078 13 14, g32p_row02_traceSegment_007_3078_0013, g32p_row02_traceSegment_007_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3105 13 14, g32p_row02_traceSegment_007_3105_0013, g32p_row02_traceSegment_007_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3078 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3078 27 27, g32p_row02_traceSegment_007_3078_0027, g32p_row02_traceSegment_007_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 3024 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3024 54 54, g32p_row02_traceSegment_007_3024_0054, g32p_row02_traceSegment_007_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3145 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3132 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3132 13 14, g32p_row02_traceSegment_007_3132_0013, g32p_row02_traceSegment_007_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3159 13 14, g32p_row02_traceSegment_007_3159_0013, g32p_row02_traceSegment_007_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3132 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3132 27 27, g32p_row02_traceSegment_007_3132_0027, g32p_row02_traceSegment_007_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3186 13 14, g32p_row02_traceSegment_007_3186_0013, g32p_row02_traceSegment_007_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3213 13 14, g32p_row02_traceSegment_007_3213_0013, g32p_row02_traceSegment_007_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3186 27 27, g32p_row02_traceSegment_007_3186_0027, g32p_row02_traceSegment_007_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 3132 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3132 54 54, g32p_row02_traceSegment_007_3132_0054, g32p_row02_traceSegment_007_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 3024 216 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3024 108 108, g32p_row02_traceSegment_007_3024_0108, g32p_row02_traceSegment_007_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3240 13 14, g32p_row02_traceSegment_007_3240_0013, g32p_row02_traceSegment_007_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3267 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3280 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3267 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3267 13 14, g32p_row02_traceSegment_007_3267_0013, g32p_row02_traceSegment_007_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3240 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3240 27 27, g32p_row02_traceSegment_007_3240_0027, g32p_row02_traceSegment_007_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3294 13 14, g32p_row02_traceSegment_007_3294_0013, g32p_row02_traceSegment_007_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3321 13 14, g32p_row02_traceSegment_007_3321_0013, g32p_row02_traceSegment_007_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3294 27 27, g32p_row02_traceSegment_007_3294_0027, g32p_row02_traceSegment_007_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 3240 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3240 54 54, g32p_row02_traceSegment_007_3240_0054, g32p_row02_traceSegment_007_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3348 13 14, g32p_row02_traceSegment_007_3348_0013, g32p_row02_traceSegment_007_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3375 13 14, g32p_row02_traceSegment_007_3375_0013, g32p_row02_traceSegment_007_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3348 27 27, g32p_row02_traceSegment_007_3348_0027, g32p_row02_traceSegment_007_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3402 13 14, g32p_row02_traceSegment_007_3402_0013, g32p_row02_traceSegment_007_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_007 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_007 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_007_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_007 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3429 13 14, g32p_row02_traceSegment_007_3429_0013, g32p_row02_traceSegment_007_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_007 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3402 27 27, g32p_row02_traceSegment_007_3402_0027, g32p_row02_traceSegment_007_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_007 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3348 54 54, g32p_row02_traceSegment_007_3348_0054, g32p_row02_traceSegment_007_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_007 3240 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3240 108 108, g32p_row02_traceSegment_007_3240_0108, g32p_row02_traceSegment_007_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_007_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_007 3024 432 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 3024 216 216, g32p_row02_traceSegment_007_3024_0216, g32p_row02_traceSegment_007_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_007_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_007 2592 864 = [0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 2592 432 432, g32p_row02_traceSegment_007_2592_0432, g32p_row02_traceSegment_007_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_007_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_007 1728 1728 = [0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 1728 864 864, g32p_row02_traceSegment_007_1728_0864, g32p_row02_traceSegment_007_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_007_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_007 0 3456 = [0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_007 0 1728 1728, g32p_row02_traceSegment_007_0000_1728, g32p_row02_traceSegment_007_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_007 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 7 = [0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_007_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_000 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 0) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 0) (g32p_literalTraceValue 1 0)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_000]
  decide +kernel

theorem g32p_row02_tracePolynomial_001 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 1) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 1) (g32p_literalTraceValue 1 1)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_001]
  decide +kernel

theorem g32p_row02_tracePolynomial_002 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 2) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 2) (g32p_literalTraceValue 1 2)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_002]
  decide +kernel

theorem g32p_row02_tracePolynomial_003 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 3) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 3) (g32p_literalTraceValue 1 3)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_003]
  decide +kernel

theorem g32p_row02_tracePolynomial_004 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 4) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 4) (g32p_literalTraceValue 1 4)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_004]
  decide +kernel

theorem g32p_row02_tracePolynomial_005 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 5) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 5) (g32p_literalTraceValue 1 5)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_005]
  decide +kernel

theorem g32p_row02_tracePolynomial_006 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 6) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 6) (g32p_literalTraceValue 1 6)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_006]
  decide +kernel

theorem g32p_row02_tracePolynomial_007 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 7) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 7) (g32p_literalTraceValue 1 7)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_007]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
