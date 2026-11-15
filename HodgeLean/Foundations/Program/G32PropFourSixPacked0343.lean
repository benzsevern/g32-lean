import HodgeLean.Foundations.Program.G32PropFourSixPacked0335
import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0342

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_092 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 92 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_092_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 13 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 0 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 0 13 14, g32p_row04_traceSegment_092_0000_0013, g32p_row04_traceSegment_092_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 27 13 14, g32p_row04_traceSegment_092_0027_0013, g32p_row04_traceSegment_092_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 0 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 0 27 27, g32p_row04_traceSegment_092_0000_0027, g32p_row04_traceSegment_092_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 54 13 14, g32p_row04_traceSegment_092_0054_0013, g32p_row04_traceSegment_092_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 81 13 14, g32p_row04_traceSegment_092_0081_0013, g32p_row04_traceSegment_092_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 54 27 27, g32p_row04_traceSegment_092_0054_0027, g32p_row04_traceSegment_092_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 0 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 0 54 54, g32p_row04_traceSegment_092_0000_0054, g32p_row04_traceSegment_092_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 108 13 14, g32p_row04_traceSegment_092_0108_0013, g32p_row04_traceSegment_092_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 135 13 14, g32p_row04_traceSegment_092_0135_0013, g32p_row04_traceSegment_092_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 108 27 27, g32p_row04_traceSegment_092_0108_0027, g32p_row04_traceSegment_092_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 162 13 14, g32p_row04_traceSegment_092_0162_0013, g32p_row04_traceSegment_092_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 202 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 189 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 189 13 14, g32p_row04_traceSegment_092_0189_0013, g32p_row04_traceSegment_092_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 162 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 162 27 27, g32p_row04_traceSegment_092_0162_0027, g32p_row04_traceSegment_092_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 108 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 108 54 54, g32p_row04_traceSegment_092_0108_0054, g32p_row04_traceSegment_092_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 0 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 0 108 108, g32p_row04_traceSegment_092_0000_0108, g32p_row04_traceSegment_092_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 216 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 216 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 216 13 14, g32p_row04_traceSegment_092_0216_0013, g32p_row04_traceSegment_092_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 243 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 256 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 243 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 243 13 14, g32p_row04_traceSegment_092_0243_0013, g32p_row04_traceSegment_092_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 216 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 216 27 27, g32p_row04_traceSegment_092_0216_0027, g32p_row04_traceSegment_092_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 270 13 14, g32p_row04_traceSegment_092_0270_0013, g32p_row04_traceSegment_092_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 297 13 14, g32p_row04_traceSegment_092_0297_0013, g32p_row04_traceSegment_092_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 270 27 27, g32p_row04_traceSegment_092_0270_0027, g32p_row04_traceSegment_092_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 216 108 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 216 54 54, g32p_row04_traceSegment_092_0216_0054, g32p_row04_traceSegment_092_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 324 13 14, g32p_row04_traceSegment_092_0324_0013, g32p_row04_traceSegment_092_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 351 13 14, g32p_row04_traceSegment_092_0351_0013, g32p_row04_traceSegment_092_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 324 27 27, g32p_row04_traceSegment_092_0324_0027, g32p_row04_traceSegment_092_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 378 13 14, g32p_row04_traceSegment_092_0378_0013, g32p_row04_traceSegment_092_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 405 13 14, g32p_row04_traceSegment_092_0405_0013, g32p_row04_traceSegment_092_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 378 27 27, g32p_row04_traceSegment_092_0378_0027, g32p_row04_traceSegment_092_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 324 54 54, g32p_row04_traceSegment_092_0324_0054, g32p_row04_traceSegment_092_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 216 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 216 108 108, g32p_row04_traceSegment_092_0216_0108, g32p_row04_traceSegment_092_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_092 0 432 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 0 216 216, g32p_row04_traceSegment_092_0000_0216, g32p_row04_traceSegment_092_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 432 13 14, g32p_row04_traceSegment_092_0432_0013, g32p_row04_traceSegment_092_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 459 13 14, g32p_row04_traceSegment_092_0459_0013, g32p_row04_traceSegment_092_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 432 27 27, g32p_row04_traceSegment_092_0432_0027, g32p_row04_traceSegment_092_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 499 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 486 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 486 13 14, g32p_row04_traceSegment_092_0486_0013, g32p_row04_traceSegment_092_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 513 13 14, g32p_row04_traceSegment_092_0513_0013, g32p_row04_traceSegment_092_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 486 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 486 27 27, g32p_row04_traceSegment_092_0486_0027, g32p_row04_traceSegment_092_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 432 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 432 54 54, g32p_row04_traceSegment_092_0432_0054, g32p_row04_traceSegment_092_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 540 13 14, g32p_row04_traceSegment_092_0540_0013, g32p_row04_traceSegment_092_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 567 13 14, g32p_row04_traceSegment_092_0567_0013, g32p_row04_traceSegment_092_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 540 27 27, g32p_row04_traceSegment_092_0540_0027, g32p_row04_traceSegment_092_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 594 13 14, g32p_row04_traceSegment_092_0594_0013, g32p_row04_traceSegment_092_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 634 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 621 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 621 13 14, g32p_row04_traceSegment_092_0621_0013, g32p_row04_traceSegment_092_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 594 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 594 27 27, g32p_row04_traceSegment_092_0594_0027, g32p_row04_traceSegment_092_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 540 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 540 54 54, g32p_row04_traceSegment_092_0540_0054, g32p_row04_traceSegment_092_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 432 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 432 108 108, g32p_row04_traceSegment_092_0432_0108, g32p_row04_traceSegment_092_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 648 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 648 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 648 13 14, g32p_row04_traceSegment_092_0648_0013, g32p_row04_traceSegment_092_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 675 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 688 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 675 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 675 13 14, g32p_row04_traceSegment_092_0675_0013, g32p_row04_traceSegment_092_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 648 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 648 27 27, g32p_row04_traceSegment_092_0648_0027, g32p_row04_traceSegment_092_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 702 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 715 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 702 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 702 13 14, g32p_row04_traceSegment_092_0702_0013, g32p_row04_traceSegment_092_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 742 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 729 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 729 13 14, g32p_row04_traceSegment_092_0729_0013, g32p_row04_traceSegment_092_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 702 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 702 27 27, g32p_row04_traceSegment_092_0702_0027, g32p_row04_traceSegment_092_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 648 108 = [8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 648 54 54, g32p_row04_traceSegment_092_0648_0054, g32p_row04_traceSegment_092_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 756 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 756 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 756 13 14, g32p_row04_traceSegment_092_0756_0013, g32p_row04_traceSegment_092_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 796 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 783 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 783 13 14, g32p_row04_traceSegment_092_0783_0013, g32p_row04_traceSegment_092_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 756 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 756 27 27, g32p_row04_traceSegment_092_0756_0027, g32p_row04_traceSegment_092_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 810 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 810 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 810 13 14, g32p_row04_traceSegment_092_0810_0013, g32p_row04_traceSegment_092_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 837 13 14, g32p_row04_traceSegment_092_0837_0013, g32p_row04_traceSegment_092_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 810 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 810 27 27, g32p_row04_traceSegment_092_0810_0027, g32p_row04_traceSegment_092_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 756 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 756 54 54, g32p_row04_traceSegment_092_0756_0054, g32p_row04_traceSegment_092_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 648 216 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 648 108 108, g32p_row04_traceSegment_092_0648_0108, g32p_row04_traceSegment_092_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_092 432 432 = [16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 432 216 216, g32p_row04_traceSegment_092_0432_0216, g32p_row04_traceSegment_092_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_092 0 864 = [16, 6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 0 432 432, g32p_row04_traceSegment_092_0000_0432, g32p_row04_traceSegment_092_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 877 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 864 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 864 13 14, g32p_row04_traceSegment_092_0864_0013, g32p_row04_traceSegment_092_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 904 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 891 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 891 13 14, g32p_row04_traceSegment_092_0891_0013, g32p_row04_traceSegment_092_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 864 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 864 27 27, g32p_row04_traceSegment_092_0864_0027, g32p_row04_traceSegment_092_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 918 13 = [0, 3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 931 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 918 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 918 13 14, g32p_row04_traceSegment_092_0918_0013, g32p_row04_traceSegment_092_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 945 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 945 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 945 13 14, g32p_row04_traceSegment_092_0945_0013, g32p_row04_traceSegment_092_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 918 54 = [0, 5] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 918 27 27, g32p_row04_traceSegment_092_0918_0027, g32p_row04_traceSegment_092_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 864 108 = [0, 8] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 864 54 54, g32p_row04_traceSegment_092_0864_0054, g32p_row04_traceSegment_092_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 972 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 985 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 972 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 972 13 14, g32p_row04_traceSegment_092_0972_0013, g32p_row04_traceSegment_092_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 999 13 14, g32p_row04_traceSegment_092_0999_0013, g32p_row04_traceSegment_092_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 972 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 972 27 27, g32p_row04_traceSegment_092_0972_0027, g32p_row04_traceSegment_092_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1026 13 14, g32p_row04_traceSegment_092_1026_0013, g32p_row04_traceSegment_092_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1053 13 14, g32p_row04_traceSegment_092_1053_0013, g32p_row04_traceSegment_092_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1026 27 27, g32p_row04_traceSegment_092_1026_0027, g32p_row04_traceSegment_092_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 972 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 972 54 54, g32p_row04_traceSegment_092_0972_0054, g32p_row04_traceSegment_092_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 864 216 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 864 108 108, g32p_row04_traceSegment_092_0864_0108, g32p_row04_traceSegment_092_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1080 13 14, g32p_row04_traceSegment_092_1080_0013, g32p_row04_traceSegment_092_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1107 13 14, g32p_row04_traceSegment_092_1107_0013, g32p_row04_traceSegment_092_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1080 27 27, g32p_row04_traceSegment_092_1080_0027, g32p_row04_traceSegment_092_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1134 13 14, g32p_row04_traceSegment_092_1134_0013, g32p_row04_traceSegment_092_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1161 13 14, g32p_row04_traceSegment_092_1161_0013, g32p_row04_traceSegment_092_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1134 27 27, g32p_row04_traceSegment_092_1134_0027, g32p_row04_traceSegment_092_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1080 54 54, g32p_row04_traceSegment_092_1080_0054, g32p_row04_traceSegment_092_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1188 13 14, g32p_row04_traceSegment_092_1188_0013, g32p_row04_traceSegment_092_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1215 13 14, g32p_row04_traceSegment_092_1215_0013, g32p_row04_traceSegment_092_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1188 27 27, g32p_row04_traceSegment_092_1188_0027, g32p_row04_traceSegment_092_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1242 13 14, g32p_row04_traceSegment_092_1242_0013, g32p_row04_traceSegment_092_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1269 13 14, g32p_row04_traceSegment_092_1269_0013, g32p_row04_traceSegment_092_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1242 27 27, g32p_row04_traceSegment_092_1242_0027, g32p_row04_traceSegment_092_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1188 54 54, g32p_row04_traceSegment_092_1188_0054, g32p_row04_traceSegment_092_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1080 108 108, g32p_row04_traceSegment_092_1080_0108, g32p_row04_traceSegment_092_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_092 864 432 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 864 216 216, g32p_row04_traceSegment_092_0864_0216, g32p_row04_traceSegment_092_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1296 13 14, g32p_row04_traceSegment_092_1296_0013, g32p_row04_traceSegment_092_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1323 13 14, g32p_row04_traceSegment_092_1323_0013, g32p_row04_traceSegment_092_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1296 27 27, g32p_row04_traceSegment_092_1296_0027, g32p_row04_traceSegment_092_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1350 13 14, g32p_row04_traceSegment_092_1350_0013, g32p_row04_traceSegment_092_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1377 13 14, g32p_row04_traceSegment_092_1377_0013, g32p_row04_traceSegment_092_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1350 27 27, g32p_row04_traceSegment_092_1350_0027, g32p_row04_traceSegment_092_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1296 54 54, g32p_row04_traceSegment_092_1296_0054, g32p_row04_traceSegment_092_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1404 13 14, g32p_row04_traceSegment_092_1404_0013, g32p_row04_traceSegment_092_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1431 13 14, g32p_row04_traceSegment_092_1431_0013, g32p_row04_traceSegment_092_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1404 27 27, g32p_row04_traceSegment_092_1404_0027, g32p_row04_traceSegment_092_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1458 13 14, g32p_row04_traceSegment_092_1458_0013, g32p_row04_traceSegment_092_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1485 13 14, g32p_row04_traceSegment_092_1485_0013, g32p_row04_traceSegment_092_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1458 27 27, g32p_row04_traceSegment_092_1458_0027, g32p_row04_traceSegment_092_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1404 54 54, g32p_row04_traceSegment_092_1404_0054, g32p_row04_traceSegment_092_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1296 108 108, g32p_row04_traceSegment_092_1296_0108, g32p_row04_traceSegment_092_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1512 13 14, g32p_row04_traceSegment_092_1512_0013, g32p_row04_traceSegment_092_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1539 13 14, g32p_row04_traceSegment_092_1539_0013, g32p_row04_traceSegment_092_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1512 27 27, g32p_row04_traceSegment_092_1512_0027, g32p_row04_traceSegment_092_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1566 13 14, g32p_row04_traceSegment_092_1566_0013, g32p_row04_traceSegment_092_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1593 13 14, g32p_row04_traceSegment_092_1593_0013, g32p_row04_traceSegment_092_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1566 27 27, g32p_row04_traceSegment_092_1566_0027, g32p_row04_traceSegment_092_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1512 54 54, g32p_row04_traceSegment_092_1512_0054, g32p_row04_traceSegment_092_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1620 13 14, g32p_row04_traceSegment_092_1620_0013, g32p_row04_traceSegment_092_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1647 13 14, g32p_row04_traceSegment_092_1647_0013, g32p_row04_traceSegment_092_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1620 27 27, g32p_row04_traceSegment_092_1620_0027, g32p_row04_traceSegment_092_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1674 13 14, g32p_row04_traceSegment_092_1674_0013, g32p_row04_traceSegment_092_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_092 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_092 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_092_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_092 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1701 13 14, g32p_row04_traceSegment_092_1701_0013, g32p_row04_traceSegment_092_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_092 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1674 27 27, g32p_row04_traceSegment_092_1674_0027, g32p_row04_traceSegment_092_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_092 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1620 54 54, g32p_row04_traceSegment_092_1620_0054, g32p_row04_traceSegment_092_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_092 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1512 108 108, g32p_row04_traceSegment_092_1512_0108, g32p_row04_traceSegment_092_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_092_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_092 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 1296 216 216, g32p_row04_traceSegment_092_1296_0216, g32p_row04_traceSegment_092_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_092 864 864 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 864 432 432, g32p_row04_traceSegment_092_0864_0432, g32p_row04_traceSegment_092_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_092_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_092 0 1728 = [16, 16] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_092 0 864 864, g32p_row04_traceSegment_092_0000_0864, g32p_row04_traceSegment_092_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_092 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 92 = [16, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_092_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_093 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 93 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_093_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 0 13 14, g32p_row04_traceSegment_093_0000_0013, g32p_row04_traceSegment_093_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 27 13 14, g32p_row04_traceSegment_093_0027_0013, g32p_row04_traceSegment_093_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 0 27 27, g32p_row04_traceSegment_093_0000_0027, g32p_row04_traceSegment_093_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 54 13 14, g32p_row04_traceSegment_093_0054_0013, g32p_row04_traceSegment_093_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 81 13 14, g32p_row04_traceSegment_093_0081_0013, g32p_row04_traceSegment_093_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 54 27 27, g32p_row04_traceSegment_093_0054_0027, g32p_row04_traceSegment_093_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 0 54 54, g32p_row04_traceSegment_093_0000_0054, g32p_row04_traceSegment_093_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 108 13 14, g32p_row04_traceSegment_093_0108_0013, g32p_row04_traceSegment_093_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 135 13 14, g32p_row04_traceSegment_093_0135_0013, g32p_row04_traceSegment_093_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 108 27 27, g32p_row04_traceSegment_093_0108_0027, g32p_row04_traceSegment_093_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 162 13 14, g32p_row04_traceSegment_093_0162_0013, g32p_row04_traceSegment_093_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 189 13 14, g32p_row04_traceSegment_093_0189_0013, g32p_row04_traceSegment_093_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 162 27 27, g32p_row04_traceSegment_093_0162_0027, g32p_row04_traceSegment_093_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 108 54 54, g32p_row04_traceSegment_093_0108_0054, g32p_row04_traceSegment_093_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 0 108 108, g32p_row04_traceSegment_093_0000_0108, g32p_row04_traceSegment_093_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 216 13 14, g32p_row04_traceSegment_093_0216_0013, g32p_row04_traceSegment_093_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 243 13 14, g32p_row04_traceSegment_093_0243_0013, g32p_row04_traceSegment_093_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 216 27 27, g32p_row04_traceSegment_093_0216_0027, g32p_row04_traceSegment_093_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 270 13 14, g32p_row04_traceSegment_093_0270_0013, g32p_row04_traceSegment_093_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 297 13 14, g32p_row04_traceSegment_093_0297_0013, g32p_row04_traceSegment_093_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 270 27 27, g32p_row04_traceSegment_093_0270_0027, g32p_row04_traceSegment_093_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 216 54 54, g32p_row04_traceSegment_093_0216_0054, g32p_row04_traceSegment_093_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 324 13 14, g32p_row04_traceSegment_093_0324_0013, g32p_row04_traceSegment_093_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 351 13 14, g32p_row04_traceSegment_093_0351_0013, g32p_row04_traceSegment_093_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 324 27 27, g32p_row04_traceSegment_093_0324_0027, g32p_row04_traceSegment_093_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 378 13 14, g32p_row04_traceSegment_093_0378_0013, g32p_row04_traceSegment_093_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 405 13 14, g32p_row04_traceSegment_093_0405_0013, g32p_row04_traceSegment_093_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 378 27 27, g32p_row04_traceSegment_093_0378_0027, g32p_row04_traceSegment_093_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 324 54 54, g32p_row04_traceSegment_093_0324_0054, g32p_row04_traceSegment_093_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 216 108 108, g32p_row04_traceSegment_093_0216_0108, g32p_row04_traceSegment_093_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_093 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 0 216 216, g32p_row04_traceSegment_093_0000_0216, g32p_row04_traceSegment_093_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 432 13 14, g32p_row04_traceSegment_093_0432_0013, g32p_row04_traceSegment_093_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 459 13 14, g32p_row04_traceSegment_093_0459_0013, g32p_row04_traceSegment_093_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 432 27 27, g32p_row04_traceSegment_093_0432_0027, g32p_row04_traceSegment_093_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 486 13 14, g32p_row04_traceSegment_093_0486_0013, g32p_row04_traceSegment_093_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 513 13 14, g32p_row04_traceSegment_093_0513_0013, g32p_row04_traceSegment_093_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 486 27 27, g32p_row04_traceSegment_093_0486_0027, g32p_row04_traceSegment_093_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 432 54 54, g32p_row04_traceSegment_093_0432_0054, g32p_row04_traceSegment_093_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 540 13 14, g32p_row04_traceSegment_093_0540_0013, g32p_row04_traceSegment_093_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 567 13 14, g32p_row04_traceSegment_093_0567_0013, g32p_row04_traceSegment_093_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 540 27 27, g32p_row04_traceSegment_093_0540_0027, g32p_row04_traceSegment_093_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 594 13 14, g32p_row04_traceSegment_093_0594_0013, g32p_row04_traceSegment_093_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 621 13 14, g32p_row04_traceSegment_093_0621_0013, g32p_row04_traceSegment_093_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 594 27 27, g32p_row04_traceSegment_093_0594_0027, g32p_row04_traceSegment_093_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 540 54 54, g32p_row04_traceSegment_093_0540_0054, g32p_row04_traceSegment_093_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 432 108 108, g32p_row04_traceSegment_093_0432_0108, g32p_row04_traceSegment_093_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 648 13 14, g32p_row04_traceSegment_093_0648_0013, g32p_row04_traceSegment_093_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 675 13 14, g32p_row04_traceSegment_093_0675_0013, g32p_row04_traceSegment_093_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 648 27 27, g32p_row04_traceSegment_093_0648_0027, g32p_row04_traceSegment_093_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 702 13 14, g32p_row04_traceSegment_093_0702_0013, g32p_row04_traceSegment_093_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 729 13 14, g32p_row04_traceSegment_093_0729_0013, g32p_row04_traceSegment_093_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 702 27 27, g32p_row04_traceSegment_093_0702_0027, g32p_row04_traceSegment_093_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 648 54 54, g32p_row04_traceSegment_093_0648_0054, g32p_row04_traceSegment_093_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 756 13 14, g32p_row04_traceSegment_093_0756_0013, g32p_row04_traceSegment_093_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 783 13 14, g32p_row04_traceSegment_093_0783_0013, g32p_row04_traceSegment_093_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 756 27 27, g32p_row04_traceSegment_093_0756_0027, g32p_row04_traceSegment_093_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 810 13 14, g32p_row04_traceSegment_093_0810_0013, g32p_row04_traceSegment_093_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 837 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 850 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 837 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 837 13 14, g32p_row04_traceSegment_093_0837_0013, g32p_row04_traceSegment_093_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 810 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 810 27 27, g32p_row04_traceSegment_093_0810_0027, g32p_row04_traceSegment_093_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 756 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 756 54 54, g32p_row04_traceSegment_093_0756_0054, g32p_row04_traceSegment_093_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 648 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 648 108 108, g32p_row04_traceSegment_093_0648_0108, g32p_row04_traceSegment_093_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_093 432 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 432 216 216, g32p_row04_traceSegment_093_0432_0216, g32p_row04_traceSegment_093_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_093 0 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 0 432 432, g32p_row04_traceSegment_093_0000_0432, g32p_row04_traceSegment_093_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 864 13 14, g32p_row04_traceSegment_093_0864_0013, g32p_row04_traceSegment_093_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 891 13 14, g32p_row04_traceSegment_093_0891_0013, g32p_row04_traceSegment_093_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 864 27 27, g32p_row04_traceSegment_093_0864_0027, g32p_row04_traceSegment_093_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 918 13 14, g32p_row04_traceSegment_093_0918_0013, g32p_row04_traceSegment_093_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 945 13 14, g32p_row04_traceSegment_093_0945_0013, g32p_row04_traceSegment_093_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 918 27 27, g32p_row04_traceSegment_093_0918_0027, g32p_row04_traceSegment_093_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 864 54 54, g32p_row04_traceSegment_093_0864_0054, g32p_row04_traceSegment_093_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 972 13 14, g32p_row04_traceSegment_093_0972_0013, g32p_row04_traceSegment_093_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 999 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 999 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 999 13 14, g32p_row04_traceSegment_093_0999_0013, g32p_row04_traceSegment_093_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 972 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 972 27 27, g32p_row04_traceSegment_093_0972_0027, g32p_row04_traceSegment_093_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1026 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1026 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1026 13 14, g32p_row04_traceSegment_093_1026_0013, g32p_row04_traceSegment_093_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1053 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1053 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1053 13 14, g32p_row04_traceSegment_093_1053_0013, g32p_row04_traceSegment_093_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1026 54 = [2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1026 27 27, g32p_row04_traceSegment_093_1026_0027, g32p_row04_traceSegment_093_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 972 108 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 972 54 54, g32p_row04_traceSegment_093_0972_0054, g32p_row04_traceSegment_093_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 864 216 = [3, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 864 108 108, g32p_row04_traceSegment_093_0864_0108, g32p_row04_traceSegment_093_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1080 13 14, g32p_row04_traceSegment_093_1080_0013, g32p_row04_traceSegment_093_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1120 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1107 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1107 13 14, g32p_row04_traceSegment_093_1107_0013, g32p_row04_traceSegment_093_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1080 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1080 27 27, g32p_row04_traceSegment_093_1080_0027, g32p_row04_traceSegment_093_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1147 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1134 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1134 13 14, g32p_row04_traceSegment_093_1134_0013, g32p_row04_traceSegment_093_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1161 13 14, g32p_row04_traceSegment_093_1161_0013, g32p_row04_traceSegment_093_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1134 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1134 27 27, g32p_row04_traceSegment_093_1134_0027, g32p_row04_traceSegment_093_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 1080 108 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1080 54 54, g32p_row04_traceSegment_093_1080_0054, g32p_row04_traceSegment_093_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1188 13 14, g32p_row04_traceSegment_093_1188_0013, g32p_row04_traceSegment_093_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1215 13 14, g32p_row04_traceSegment_093_1215_0013, g32p_row04_traceSegment_093_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1188 27 27, g32p_row04_traceSegment_093_1188_0027, g32p_row04_traceSegment_093_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1242 13 14, g32p_row04_traceSegment_093_1242_0013, g32p_row04_traceSegment_093_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1269 13 14, g32p_row04_traceSegment_093_1269_0013, g32p_row04_traceSegment_093_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1242 27 27, g32p_row04_traceSegment_093_1242_0027, g32p_row04_traceSegment_093_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1188 54 54, g32p_row04_traceSegment_093_1188_0054, g32p_row04_traceSegment_093_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 1080 216 = [1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1080 108 108, g32p_row04_traceSegment_093_1080_0108, g32p_row04_traceSegment_093_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_093 864 432 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 864 216 216, g32p_row04_traceSegment_093_0864_0216, g32p_row04_traceSegment_093_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1296 13 14, g32p_row04_traceSegment_093_1296_0013, g32p_row04_traceSegment_093_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1323 13 14, g32p_row04_traceSegment_093_1323_0013, g32p_row04_traceSegment_093_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1296 27 27, g32p_row04_traceSegment_093_1296_0027, g32p_row04_traceSegment_093_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1350 13 14, g32p_row04_traceSegment_093_1350_0013, g32p_row04_traceSegment_093_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1377 13 14, g32p_row04_traceSegment_093_1377_0013, g32p_row04_traceSegment_093_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1350 27 27, g32p_row04_traceSegment_093_1350_0027, g32p_row04_traceSegment_093_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1296 54 54, g32p_row04_traceSegment_093_1296_0054, g32p_row04_traceSegment_093_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1404 13 14, g32p_row04_traceSegment_093_1404_0013, g32p_row04_traceSegment_093_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1431 13 14, g32p_row04_traceSegment_093_1431_0013, g32p_row04_traceSegment_093_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1404 27 27, g32p_row04_traceSegment_093_1404_0027, g32p_row04_traceSegment_093_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1458 13 14, g32p_row04_traceSegment_093_1458_0013, g32p_row04_traceSegment_093_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1485 13 14, g32p_row04_traceSegment_093_1485_0013, g32p_row04_traceSegment_093_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1458 27 27, g32p_row04_traceSegment_093_1458_0027, g32p_row04_traceSegment_093_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1404 54 54, g32p_row04_traceSegment_093_1404_0054, g32p_row04_traceSegment_093_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1296 108 108, g32p_row04_traceSegment_093_1296_0108, g32p_row04_traceSegment_093_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1512 13 14, g32p_row04_traceSegment_093_1512_0013, g32p_row04_traceSegment_093_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1539 13 14, g32p_row04_traceSegment_093_1539_0013, g32p_row04_traceSegment_093_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1512 27 27, g32p_row04_traceSegment_093_1512_0027, g32p_row04_traceSegment_093_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1566 13 14, g32p_row04_traceSegment_093_1566_0013, g32p_row04_traceSegment_093_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1593 13 14, g32p_row04_traceSegment_093_1593_0013, g32p_row04_traceSegment_093_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1566 27 27, g32p_row04_traceSegment_093_1566_0027, g32p_row04_traceSegment_093_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1512 54 54, g32p_row04_traceSegment_093_1512_0054, g32p_row04_traceSegment_093_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1620 13 14, g32p_row04_traceSegment_093_1620_0013, g32p_row04_traceSegment_093_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1647 13 14, g32p_row04_traceSegment_093_1647_0013, g32p_row04_traceSegment_093_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1620 27 27, g32p_row04_traceSegment_093_1620_0027, g32p_row04_traceSegment_093_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1674 13 14, g32p_row04_traceSegment_093_1674_0013, g32p_row04_traceSegment_093_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_093 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_093 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_093_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_093 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1701 13 14, g32p_row04_traceSegment_093_1701_0013, g32p_row04_traceSegment_093_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_093 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1674 27 27, g32p_row04_traceSegment_093_1674_0027, g32p_row04_traceSegment_093_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_093 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1620 54 54, g32p_row04_traceSegment_093_1620_0054, g32p_row04_traceSegment_093_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_093 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1512 108 108, g32p_row04_traceSegment_093_1512_0108, g32p_row04_traceSegment_093_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_093_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_093 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 1296 216 216, g32p_row04_traceSegment_093_1296_0216, g32p_row04_traceSegment_093_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_093 864 864 = [4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 864 432 432, g32p_row04_traceSegment_093_0864_0432, g32p_row04_traceSegment_093_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_093_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_093 0 1728 = [4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_093 0 864 864, g32p_row04_traceSegment_093_0000_0864, g32p_row04_traceSegment_093_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_093 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 93 = [4, 0, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_093_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_094 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 94 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_094_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 0 13 14, g32p_row04_traceSegment_094_0000_0013, g32p_row04_traceSegment_094_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 27 13 14, g32p_row04_traceSegment_094_0027_0013, g32p_row04_traceSegment_094_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 0 27 27, g32p_row04_traceSegment_094_0000_0027, g32p_row04_traceSegment_094_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 54 13 14, g32p_row04_traceSegment_094_0054_0013, g32p_row04_traceSegment_094_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 81 13 14, g32p_row04_traceSegment_094_0081_0013, g32p_row04_traceSegment_094_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 54 27 27, g32p_row04_traceSegment_094_0054_0027, g32p_row04_traceSegment_094_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 0 54 54, g32p_row04_traceSegment_094_0000_0054, g32p_row04_traceSegment_094_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 108 13 14, g32p_row04_traceSegment_094_0108_0013, g32p_row04_traceSegment_094_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 135 13 14, g32p_row04_traceSegment_094_0135_0013, g32p_row04_traceSegment_094_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 108 27 27, g32p_row04_traceSegment_094_0108_0027, g32p_row04_traceSegment_094_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 162 13 14, g32p_row04_traceSegment_094_0162_0013, g32p_row04_traceSegment_094_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 189 13 14, g32p_row04_traceSegment_094_0189_0013, g32p_row04_traceSegment_094_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 162 27 27, g32p_row04_traceSegment_094_0162_0027, g32p_row04_traceSegment_094_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 108 54 54, g32p_row04_traceSegment_094_0108_0054, g32p_row04_traceSegment_094_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 0 108 108, g32p_row04_traceSegment_094_0000_0108, g32p_row04_traceSegment_094_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 216 13 14, g32p_row04_traceSegment_094_0216_0013, g32p_row04_traceSegment_094_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 243 13 14, g32p_row04_traceSegment_094_0243_0013, g32p_row04_traceSegment_094_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 216 27 27, g32p_row04_traceSegment_094_0216_0027, g32p_row04_traceSegment_094_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 270 13 14, g32p_row04_traceSegment_094_0270_0013, g32p_row04_traceSegment_094_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 297 13 14, g32p_row04_traceSegment_094_0297_0013, g32p_row04_traceSegment_094_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 270 27 27, g32p_row04_traceSegment_094_0270_0027, g32p_row04_traceSegment_094_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 216 54 54, g32p_row04_traceSegment_094_0216_0054, g32p_row04_traceSegment_094_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 324 13 14, g32p_row04_traceSegment_094_0324_0013, g32p_row04_traceSegment_094_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 351 13 14, g32p_row04_traceSegment_094_0351_0013, g32p_row04_traceSegment_094_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 324 27 27, g32p_row04_traceSegment_094_0324_0027, g32p_row04_traceSegment_094_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 378 13 14, g32p_row04_traceSegment_094_0378_0013, g32p_row04_traceSegment_094_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 405 13 14, g32p_row04_traceSegment_094_0405_0013, g32p_row04_traceSegment_094_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 378 27 27, g32p_row04_traceSegment_094_0378_0027, g32p_row04_traceSegment_094_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 324 54 54, g32p_row04_traceSegment_094_0324_0054, g32p_row04_traceSegment_094_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 216 108 108, g32p_row04_traceSegment_094_0216_0108, g32p_row04_traceSegment_094_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_094 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 0 216 216, g32p_row04_traceSegment_094_0000_0216, g32p_row04_traceSegment_094_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 432 13 14, g32p_row04_traceSegment_094_0432_0013, g32p_row04_traceSegment_094_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 459 13 14, g32p_row04_traceSegment_094_0459_0013, g32p_row04_traceSegment_094_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 432 27 27, g32p_row04_traceSegment_094_0432_0027, g32p_row04_traceSegment_094_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 486 13 14, g32p_row04_traceSegment_094_0486_0013, g32p_row04_traceSegment_094_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 513 13 14, g32p_row04_traceSegment_094_0513_0013, g32p_row04_traceSegment_094_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 486 27 27, g32p_row04_traceSegment_094_0486_0027, g32p_row04_traceSegment_094_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 432 54 54, g32p_row04_traceSegment_094_0432_0054, g32p_row04_traceSegment_094_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 540 13 14, g32p_row04_traceSegment_094_0540_0013, g32p_row04_traceSegment_094_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 567 13 14, g32p_row04_traceSegment_094_0567_0013, g32p_row04_traceSegment_094_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 540 27 27, g32p_row04_traceSegment_094_0540_0027, g32p_row04_traceSegment_094_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 594 13 14, g32p_row04_traceSegment_094_0594_0013, g32p_row04_traceSegment_094_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 621 13 14, g32p_row04_traceSegment_094_0621_0013, g32p_row04_traceSegment_094_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 594 27 27, g32p_row04_traceSegment_094_0594_0027, g32p_row04_traceSegment_094_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 540 54 54, g32p_row04_traceSegment_094_0540_0054, g32p_row04_traceSegment_094_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 432 108 108, g32p_row04_traceSegment_094_0432_0108, g32p_row04_traceSegment_094_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 648 13 14, g32p_row04_traceSegment_094_0648_0013, g32p_row04_traceSegment_094_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 675 13 14, g32p_row04_traceSegment_094_0675_0013, g32p_row04_traceSegment_094_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 648 27 27, g32p_row04_traceSegment_094_0648_0027, g32p_row04_traceSegment_094_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 702 13 14, g32p_row04_traceSegment_094_0702_0013, g32p_row04_traceSegment_094_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 729 13 14, g32p_row04_traceSegment_094_0729_0013, g32p_row04_traceSegment_094_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 702 27 27, g32p_row04_traceSegment_094_0702_0027, g32p_row04_traceSegment_094_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 648 54 54, g32p_row04_traceSegment_094_0648_0054, g32p_row04_traceSegment_094_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 756 13 14, g32p_row04_traceSegment_094_0756_0013, g32p_row04_traceSegment_094_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 783 13 14, g32p_row04_traceSegment_094_0783_0013, g32p_row04_traceSegment_094_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 756 27 27, g32p_row04_traceSegment_094_0756_0027, g32p_row04_traceSegment_094_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 810 13 14, g32p_row04_traceSegment_094_0810_0013, g32p_row04_traceSegment_094_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 837 13 14, g32p_row04_traceSegment_094_0837_0013, g32p_row04_traceSegment_094_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 810 27 27, g32p_row04_traceSegment_094_0810_0027, g32p_row04_traceSegment_094_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 756 54 54, g32p_row04_traceSegment_094_0756_0054, g32p_row04_traceSegment_094_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 648 108 108, g32p_row04_traceSegment_094_0648_0108, g32p_row04_traceSegment_094_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_094 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 432 216 216, g32p_row04_traceSegment_094_0432_0216, g32p_row04_traceSegment_094_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_094 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 0 432 432, g32p_row04_traceSegment_094_0000_0432, g32p_row04_traceSegment_094_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 864 13 14, g32p_row04_traceSegment_094_0864_0013, g32p_row04_traceSegment_094_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 891 13 14, g32p_row04_traceSegment_094_0891_0013, g32p_row04_traceSegment_094_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 864 27 27, g32p_row04_traceSegment_094_0864_0027, g32p_row04_traceSegment_094_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 918 13 14, g32p_row04_traceSegment_094_0918_0013, g32p_row04_traceSegment_094_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 945 13 14, g32p_row04_traceSegment_094_0945_0013, g32p_row04_traceSegment_094_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 918 27 27, g32p_row04_traceSegment_094_0918_0027, g32p_row04_traceSegment_094_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 864 54 54, g32p_row04_traceSegment_094_0864_0054, g32p_row04_traceSegment_094_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 972 13 14, g32p_row04_traceSegment_094_0972_0013, g32p_row04_traceSegment_094_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 999 13 14, g32p_row04_traceSegment_094_0999_0013, g32p_row04_traceSegment_094_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 972 27 27, g32p_row04_traceSegment_094_0972_0027, g32p_row04_traceSegment_094_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1039 14 = [3] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1026 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1026 13 14, g32p_row04_traceSegment_094_1026_0013, g32p_row04_traceSegment_094_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1053 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1066 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1053 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1053 13 14, g32p_row04_traceSegment_094_1053_0013, g32p_row04_traceSegment_094_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1026 54 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1026 27 27, g32p_row04_traceSegment_094_1026_0027, g32p_row04_traceSegment_094_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 972 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 972 54 54, g32p_row04_traceSegment_094_0972_0054, g32p_row04_traceSegment_094_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 864 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 864 108 108, g32p_row04_traceSegment_094_0864_0108, g32p_row04_traceSegment_094_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1080 13 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1080 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1080 13 14, g32p_row04_traceSegment_094_1080_0013, g32p_row04_traceSegment_094_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1107 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1120 14 = [2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1107 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1107 13 14, g32p_row04_traceSegment_094_1107_0013, g32p_row04_traceSegment_094_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1080 54 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1080 27 27, g32p_row04_traceSegment_094_1080_0027, g32p_row04_traceSegment_094_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1134 13 14, g32p_row04_traceSegment_094_1134_0013, g32p_row04_traceSegment_094_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1161 13 14, g32p_row04_traceSegment_094_1161_0013, g32p_row04_traceSegment_094_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1134 27 27, g32p_row04_traceSegment_094_1134_0027, g32p_row04_traceSegment_094_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 1080 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1080 54 54, g32p_row04_traceSegment_094_1080_0054, g32p_row04_traceSegment_094_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1188 13 14, g32p_row04_traceSegment_094_1188_0013, g32p_row04_traceSegment_094_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1215 13 14, g32p_row04_traceSegment_094_1215_0013, g32p_row04_traceSegment_094_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1188 27 27, g32p_row04_traceSegment_094_1188_0027, g32p_row04_traceSegment_094_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1242 13 14, g32p_row04_traceSegment_094_1242_0013, g32p_row04_traceSegment_094_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1269 13 14, g32p_row04_traceSegment_094_1269_0013, g32p_row04_traceSegment_094_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1242 27 27, g32p_row04_traceSegment_094_1242_0027, g32p_row04_traceSegment_094_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1188 54 54, g32p_row04_traceSegment_094_1188_0054, g32p_row04_traceSegment_094_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 1080 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1080 108 108, g32p_row04_traceSegment_094_1080_0108, g32p_row04_traceSegment_094_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_094 864 432 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 864 216 216, g32p_row04_traceSegment_094_0864_0216, g32p_row04_traceSegment_094_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1296 13 14, g32p_row04_traceSegment_094_1296_0013, g32p_row04_traceSegment_094_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1323 13 14, g32p_row04_traceSegment_094_1323_0013, g32p_row04_traceSegment_094_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1296 27 27, g32p_row04_traceSegment_094_1296_0027, g32p_row04_traceSegment_094_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1350 13 14, g32p_row04_traceSegment_094_1350_0013, g32p_row04_traceSegment_094_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1377 13 14, g32p_row04_traceSegment_094_1377_0013, g32p_row04_traceSegment_094_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1350 27 27, g32p_row04_traceSegment_094_1350_0027, g32p_row04_traceSegment_094_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1296 54 54, g32p_row04_traceSegment_094_1296_0054, g32p_row04_traceSegment_094_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1404 13 14, g32p_row04_traceSegment_094_1404_0013, g32p_row04_traceSegment_094_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1431 13 14, g32p_row04_traceSegment_094_1431_0013, g32p_row04_traceSegment_094_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1404 27 27, g32p_row04_traceSegment_094_1404_0027, g32p_row04_traceSegment_094_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1458 13 14, g32p_row04_traceSegment_094_1458_0013, g32p_row04_traceSegment_094_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1485 13 14, g32p_row04_traceSegment_094_1485_0013, g32p_row04_traceSegment_094_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1458 27 27, g32p_row04_traceSegment_094_1458_0027, g32p_row04_traceSegment_094_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1404 54 54, g32p_row04_traceSegment_094_1404_0054, g32p_row04_traceSegment_094_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1296 108 108, g32p_row04_traceSegment_094_1296_0108, g32p_row04_traceSegment_094_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1512 13 14, g32p_row04_traceSegment_094_1512_0013, g32p_row04_traceSegment_094_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1539 13 14, g32p_row04_traceSegment_094_1539_0013, g32p_row04_traceSegment_094_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1512 27 27, g32p_row04_traceSegment_094_1512_0027, g32p_row04_traceSegment_094_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1566 13 14, g32p_row04_traceSegment_094_1566_0013, g32p_row04_traceSegment_094_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1593 13 14, g32p_row04_traceSegment_094_1593_0013, g32p_row04_traceSegment_094_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1566 27 27, g32p_row04_traceSegment_094_1566_0027, g32p_row04_traceSegment_094_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1512 54 54, g32p_row04_traceSegment_094_1512_0054, g32p_row04_traceSegment_094_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1620 13 14, g32p_row04_traceSegment_094_1620_0013, g32p_row04_traceSegment_094_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1647 13 14, g32p_row04_traceSegment_094_1647_0013, g32p_row04_traceSegment_094_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1620 27 27, g32p_row04_traceSegment_094_1620_0027, g32p_row04_traceSegment_094_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1674 13 14, g32p_row04_traceSegment_094_1674_0013, g32p_row04_traceSegment_094_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_094 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_094 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_094_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_094 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1701 13 14, g32p_row04_traceSegment_094_1701_0013, g32p_row04_traceSegment_094_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_094 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1674 27 27, g32p_row04_traceSegment_094_1674_0027, g32p_row04_traceSegment_094_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_094 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1620 54 54, g32p_row04_traceSegment_094_1620_0054, g32p_row04_traceSegment_094_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_094 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1512 108 108, g32p_row04_traceSegment_094_1512_0108, g32p_row04_traceSegment_094_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_094_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_094 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 1296 216 216, g32p_row04_traceSegment_094_1296_0216, g32p_row04_traceSegment_094_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_094 864 864 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 864 432 432, g32p_row04_traceSegment_094_0864_0432, g32p_row04_traceSegment_094_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_094_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_094 0 1728 = [12] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_094 0 864 864, g32p_row04_traceSegment_094_0000_0864, g32p_row04_traceSegment_094_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_094 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 94 = [12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_094_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_095 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 95 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_095_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 0 13 14, g32p_row04_traceSegment_095_0000_0013, g32p_row04_traceSegment_095_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 27 13 14, g32p_row04_traceSegment_095_0027_0013, g32p_row04_traceSegment_095_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 0 27 27, g32p_row04_traceSegment_095_0000_0027, g32p_row04_traceSegment_095_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 67 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 54 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 54 13 14, g32p_row04_traceSegment_095_0054_0013, g32p_row04_traceSegment_095_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 81 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 81 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 81 13 14, g32p_row04_traceSegment_095_0081_0013, g32p_row04_traceSegment_095_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 54 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 54 27 27, g32p_row04_traceSegment_095_0054_0027, g32p_row04_traceSegment_095_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 0 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 0 54 54, g32p_row04_traceSegment_095_0000_0054, g32p_row04_traceSegment_095_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 108 13 14, g32p_row04_traceSegment_095_0108_0013, g32p_row04_traceSegment_095_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 135 13 14, g32p_row04_traceSegment_095_0135_0013, g32p_row04_traceSegment_095_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 108 27 27, g32p_row04_traceSegment_095_0108_0027, g32p_row04_traceSegment_095_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 162 13 14, g32p_row04_traceSegment_095_0162_0013, g32p_row04_traceSegment_095_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 189 13 14, g32p_row04_traceSegment_095_0189_0013, g32p_row04_traceSegment_095_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 162 27 27, g32p_row04_traceSegment_095_0162_0027, g32p_row04_traceSegment_095_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 108 54 54, g32p_row04_traceSegment_095_0108_0054, g32p_row04_traceSegment_095_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 0 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 0 108 108, g32p_row04_traceSegment_095_0000_0108, g32p_row04_traceSegment_095_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 216 13 14, g32p_row04_traceSegment_095_0216_0013, g32p_row04_traceSegment_095_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 243 13 14, g32p_row04_traceSegment_095_0243_0013, g32p_row04_traceSegment_095_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 216 27 27, g32p_row04_traceSegment_095_0216_0027, g32p_row04_traceSegment_095_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 270 13 14, g32p_row04_traceSegment_095_0270_0013, g32p_row04_traceSegment_095_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 297 13 14, g32p_row04_traceSegment_095_0297_0013, g32p_row04_traceSegment_095_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 270 27 27, g32p_row04_traceSegment_095_0270_0027, g32p_row04_traceSegment_095_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 216 54 54, g32p_row04_traceSegment_095_0216_0054, g32p_row04_traceSegment_095_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 324 13 14, g32p_row04_traceSegment_095_0324_0013, g32p_row04_traceSegment_095_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 351 13 14, g32p_row04_traceSegment_095_0351_0013, g32p_row04_traceSegment_095_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 324 27 27, g32p_row04_traceSegment_095_0324_0027, g32p_row04_traceSegment_095_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 378 13 14, g32p_row04_traceSegment_095_0378_0013, g32p_row04_traceSegment_095_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 405 13 14, g32p_row04_traceSegment_095_0405_0013, g32p_row04_traceSegment_095_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 378 27 27, g32p_row04_traceSegment_095_0378_0027, g32p_row04_traceSegment_095_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 324 54 54, g32p_row04_traceSegment_095_0324_0054, g32p_row04_traceSegment_095_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 216 108 108, g32p_row04_traceSegment_095_0216_0108, g32p_row04_traceSegment_095_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_095 0 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 0 216 216, g32p_row04_traceSegment_095_0000_0216, g32p_row04_traceSegment_095_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 432 13 14, g32p_row04_traceSegment_095_0432_0013, g32p_row04_traceSegment_095_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 459 13 14, g32p_row04_traceSegment_095_0459_0013, g32p_row04_traceSegment_095_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 432 27 27, g32p_row04_traceSegment_095_0432_0027, g32p_row04_traceSegment_095_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 499 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 486 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 486 13 14, g32p_row04_traceSegment_095_0486_0013, g32p_row04_traceSegment_095_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 513 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 513 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 513 13 14, g32p_row04_traceSegment_095_0513_0013, g32p_row04_traceSegment_095_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 486 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 486 27 27, g32p_row04_traceSegment_095_0486_0027, g32p_row04_traceSegment_095_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 432 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 432 54 54, g32p_row04_traceSegment_095_0432_0054, g32p_row04_traceSegment_095_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 540 13 14, g32p_row04_traceSegment_095_0540_0013, g32p_row04_traceSegment_095_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 567 13 14, g32p_row04_traceSegment_095_0567_0013, g32p_row04_traceSegment_095_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 540 27 27, g32p_row04_traceSegment_095_0540_0027, g32p_row04_traceSegment_095_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 594 13 14, g32p_row04_traceSegment_095_0594_0013, g32p_row04_traceSegment_095_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 634 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 621 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 621 13 14, g32p_row04_traceSegment_095_0621_0013, g32p_row04_traceSegment_095_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 594 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 594 27 27, g32p_row04_traceSegment_095_0594_0027, g32p_row04_traceSegment_095_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 540 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 540 54 54, g32p_row04_traceSegment_095_0540_0054, g32p_row04_traceSegment_095_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 432 216 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 432 108 108, g32p_row04_traceSegment_095_0432_0108, g32p_row04_traceSegment_095_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 648 13 14, g32p_row04_traceSegment_095_0648_0013, g32p_row04_traceSegment_095_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 675 13 14, g32p_row04_traceSegment_095_0675_0013, g32p_row04_traceSegment_095_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 648 27 27, g32p_row04_traceSegment_095_0648_0027, g32p_row04_traceSegment_095_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 715 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 702 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 702 13 14, g32p_row04_traceSegment_095_0702_0013, g32p_row04_traceSegment_095_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 729 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 729 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 729 13 14, g32p_row04_traceSegment_095_0729_0013, g32p_row04_traceSegment_095_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 702 54 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 702 27 27, g32p_row04_traceSegment_095_0702_0027, g32p_row04_traceSegment_095_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 648 108 = [1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 648 54 54, g32p_row04_traceSegment_095_0648_0054, g32p_row04_traceSegment_095_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 756 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 756 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 756 13 14, g32p_row04_traceSegment_095_0756_0013, g32p_row04_traceSegment_095_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 783 13 14, g32p_row04_traceSegment_095_0783_0013, g32p_row04_traceSegment_095_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 756 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 756 27 27, g32p_row04_traceSegment_095_0756_0027, g32p_row04_traceSegment_095_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 810 13 14, g32p_row04_traceSegment_095_0810_0013, g32p_row04_traceSegment_095_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 837 13 14, g32p_row04_traceSegment_095_0837_0013, g32p_row04_traceSegment_095_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 810 27 27, g32p_row04_traceSegment_095_0810_0027, g32p_row04_traceSegment_095_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 756 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 756 54 54, g32p_row04_traceSegment_095_0756_0054, g32p_row04_traceSegment_095_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 648 216 = [2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 648 108 108, g32p_row04_traceSegment_095_0648_0108, g32p_row04_traceSegment_095_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_095 432 432 = [2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 432 216 216, g32p_row04_traceSegment_095_0432_0216, g32p_row04_traceSegment_095_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_095 0 864 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 0 432 432, g32p_row04_traceSegment_095_0000_0432, g32p_row04_traceSegment_095_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 864 13 14, g32p_row04_traceSegment_095_0864_0013, g32p_row04_traceSegment_095_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 891 13 14, g32p_row04_traceSegment_095_0891_0013, g32p_row04_traceSegment_095_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 864 27 27, g32p_row04_traceSegment_095_0864_0027, g32p_row04_traceSegment_095_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 918 13 14, g32p_row04_traceSegment_095_0918_0013, g32p_row04_traceSegment_095_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 945 13 14, g32p_row04_traceSegment_095_0945_0013, g32p_row04_traceSegment_095_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 918 27 27, g32p_row04_traceSegment_095_0918_0027, g32p_row04_traceSegment_095_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 864 54 54, g32p_row04_traceSegment_095_0864_0054, g32p_row04_traceSegment_095_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 972 13 14, g32p_row04_traceSegment_095_0972_0013, g32p_row04_traceSegment_095_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 999 13 14, g32p_row04_traceSegment_095_0999_0013, g32p_row04_traceSegment_095_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 972 27 27, g32p_row04_traceSegment_095_0972_0027, g32p_row04_traceSegment_095_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1026 13 14, g32p_row04_traceSegment_095_1026_0013, g32p_row04_traceSegment_095_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1053 13 14, g32p_row04_traceSegment_095_1053_0013, g32p_row04_traceSegment_095_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1026 27 27, g32p_row04_traceSegment_095_1026_0027, g32p_row04_traceSegment_095_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 972 54 54, g32p_row04_traceSegment_095_0972_0054, g32p_row04_traceSegment_095_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 864 108 108, g32p_row04_traceSegment_095_0864_0108, g32p_row04_traceSegment_095_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1080 13 14, g32p_row04_traceSegment_095_1080_0013, g32p_row04_traceSegment_095_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1107 13 14, g32p_row04_traceSegment_095_1107_0013, g32p_row04_traceSegment_095_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1080 27 27, g32p_row04_traceSegment_095_1080_0027, g32p_row04_traceSegment_095_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1134 13 14, g32p_row04_traceSegment_095_1134_0013, g32p_row04_traceSegment_095_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1161 13 14, g32p_row04_traceSegment_095_1161_0013, g32p_row04_traceSegment_095_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1134 27 27, g32p_row04_traceSegment_095_1134_0027, g32p_row04_traceSegment_095_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1080 54 54, g32p_row04_traceSegment_095_1080_0054, g32p_row04_traceSegment_095_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1188 13 14, g32p_row04_traceSegment_095_1188_0013, g32p_row04_traceSegment_095_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1215 13 14, g32p_row04_traceSegment_095_1215_0013, g32p_row04_traceSegment_095_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1188 27 27, g32p_row04_traceSegment_095_1188_0027, g32p_row04_traceSegment_095_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1242 13 14, g32p_row04_traceSegment_095_1242_0013, g32p_row04_traceSegment_095_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1269 13 14, g32p_row04_traceSegment_095_1269_0013, g32p_row04_traceSegment_095_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1242 27 27, g32p_row04_traceSegment_095_1242_0027, g32p_row04_traceSegment_095_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1188 54 54, g32p_row04_traceSegment_095_1188_0054, g32p_row04_traceSegment_095_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1080 108 108, g32p_row04_traceSegment_095_1080_0108, g32p_row04_traceSegment_095_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_095 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 864 216 216, g32p_row04_traceSegment_095_0864_0216, g32p_row04_traceSegment_095_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1296 13 14, g32p_row04_traceSegment_095_1296_0013, g32p_row04_traceSegment_095_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1323 13 14, g32p_row04_traceSegment_095_1323_0013, g32p_row04_traceSegment_095_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1296 27 27, g32p_row04_traceSegment_095_1296_0027, g32p_row04_traceSegment_095_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1350 13 14, g32p_row04_traceSegment_095_1350_0013, g32p_row04_traceSegment_095_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1377 13 14, g32p_row04_traceSegment_095_1377_0013, g32p_row04_traceSegment_095_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1350 27 27, g32p_row04_traceSegment_095_1350_0027, g32p_row04_traceSegment_095_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1296 54 54, g32p_row04_traceSegment_095_1296_0054, g32p_row04_traceSegment_095_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1404 13 14, g32p_row04_traceSegment_095_1404_0013, g32p_row04_traceSegment_095_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1431 13 14, g32p_row04_traceSegment_095_1431_0013, g32p_row04_traceSegment_095_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1404 27 27, g32p_row04_traceSegment_095_1404_0027, g32p_row04_traceSegment_095_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1458 13 14, g32p_row04_traceSegment_095_1458_0013, g32p_row04_traceSegment_095_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1485 13 14, g32p_row04_traceSegment_095_1485_0013, g32p_row04_traceSegment_095_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1458 27 27, g32p_row04_traceSegment_095_1458_0027, g32p_row04_traceSegment_095_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1404 54 54, g32p_row04_traceSegment_095_1404_0054, g32p_row04_traceSegment_095_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1296 108 108, g32p_row04_traceSegment_095_1296_0108, g32p_row04_traceSegment_095_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1512 13 14, g32p_row04_traceSegment_095_1512_0013, g32p_row04_traceSegment_095_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1539 13 14, g32p_row04_traceSegment_095_1539_0013, g32p_row04_traceSegment_095_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1512 27 27, g32p_row04_traceSegment_095_1512_0027, g32p_row04_traceSegment_095_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1566 13 14, g32p_row04_traceSegment_095_1566_0013, g32p_row04_traceSegment_095_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1593 13 14, g32p_row04_traceSegment_095_1593_0013, g32p_row04_traceSegment_095_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1566 27 27, g32p_row04_traceSegment_095_1566_0027, g32p_row04_traceSegment_095_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1512 54 54, g32p_row04_traceSegment_095_1512_0054, g32p_row04_traceSegment_095_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1620 13 14, g32p_row04_traceSegment_095_1620_0013, g32p_row04_traceSegment_095_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1647 13 14, g32p_row04_traceSegment_095_1647_0013, g32p_row04_traceSegment_095_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1620 27 27, g32p_row04_traceSegment_095_1620_0027, g32p_row04_traceSegment_095_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1674 13 14, g32p_row04_traceSegment_095_1674_0013, g32p_row04_traceSegment_095_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_095 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_095 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_095_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_095 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1701 13 14, g32p_row04_traceSegment_095_1701_0013, g32p_row04_traceSegment_095_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_095 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1674 27 27, g32p_row04_traceSegment_095_1674_0027, g32p_row04_traceSegment_095_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_095 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1620 54 54, g32p_row04_traceSegment_095_1620_0054, g32p_row04_traceSegment_095_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_095 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1512 108 108, g32p_row04_traceSegment_095_1512_0108, g32p_row04_traceSegment_095_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_095_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_095 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 1296 216 216, g32p_row04_traceSegment_095_1296_0216, g32p_row04_traceSegment_095_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_095 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 864 432 432, g32p_row04_traceSegment_095_0864_0432, g32p_row04_traceSegment_095_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_095_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_095 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_095 0 864 864, g32p_row04_traceSegment_095_0000_0864, g32p_row04_traceSegment_095_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_095 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 95 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_095_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row04_tracePolynomial_088 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 88) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 88) (g32p_literalTraceValue 3 88)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_088]
  decide +kernel

theorem g32p_row04_tracePolynomial_089 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 89) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 89) (g32p_literalTraceValue 3 89)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_089]
  decide +kernel

theorem g32p_row04_tracePolynomial_090 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 90) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 90) (g32p_literalTraceValue 3 90)
      [1, 1, 1] [3456] = true := by
  rw [g32p_row04_traceCoefficients_090]
  decide +kernel

theorem g32p_row04_tracePolynomial_091 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 91) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 91) (g32p_literalTraceValue 3 91)
      [1, 1, 1] [1728] = true := by
  rw [g32p_row04_traceCoefficients_091]
  decide +kernel

theorem g32p_row04_tracePolynomial_092 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 92) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 92) (g32p_literalTraceValue 3 92)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_092]
  decide +kernel

theorem g32p_row04_tracePolynomial_093 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 93) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 93) (g32p_literalTraceValue 3 93)
      [1, 1, 1] [15552] = true := by
  rw [g32p_row04_traceCoefficients_093]
  decide +kernel

theorem g32p_row04_tracePolynomial_094 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 94) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 94) (g32p_literalTraceValue 3 94)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_094]
  decide +kernel

theorem g32p_row04_tracePolynomial_095 :
    g32p_supplierTracePolynomialCheck 1728 (g32p_literalCentralizer 95) 3
      (g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 95) (g32p_literalTraceValue 3 95)
      [1, 1, 1] [] = true := by
  rw [g32p_row04_traceCoefficients_095]
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

private def g32p_row04_traceSegment_096 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 96 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_096_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 0 13 14, g32p_row04_traceSegment_096_0000_0013, g32p_row04_traceSegment_096_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 27 13 14, g32p_row04_traceSegment_096_0027_0013, g32p_row04_traceSegment_096_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 0 27 27, g32p_row04_traceSegment_096_0000_0027, g32p_row04_traceSegment_096_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 54 13 14, g32p_row04_traceSegment_096_0054_0013, g32p_row04_traceSegment_096_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 81 13 14, g32p_row04_traceSegment_096_0081_0013, g32p_row04_traceSegment_096_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 54 27 27, g32p_row04_traceSegment_096_0054_0027, g32p_row04_traceSegment_096_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 0 54 54, g32p_row04_traceSegment_096_0000_0054, g32p_row04_traceSegment_096_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 108 13 14, g32p_row04_traceSegment_096_0108_0013, g32p_row04_traceSegment_096_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 135 13 14, g32p_row04_traceSegment_096_0135_0013, g32p_row04_traceSegment_096_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 108 27 27, g32p_row04_traceSegment_096_0108_0027, g32p_row04_traceSegment_096_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 162 13 14, g32p_row04_traceSegment_096_0162_0013, g32p_row04_traceSegment_096_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 189 13 14, g32p_row04_traceSegment_096_0189_0013, g32p_row04_traceSegment_096_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 162 27 27, g32p_row04_traceSegment_096_0162_0027, g32p_row04_traceSegment_096_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 108 54 54, g32p_row04_traceSegment_096_0108_0054, g32p_row04_traceSegment_096_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 0 108 108, g32p_row04_traceSegment_096_0000_0108, g32p_row04_traceSegment_096_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 216 13 14, g32p_row04_traceSegment_096_0216_0013, g32p_row04_traceSegment_096_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 243 13 14, g32p_row04_traceSegment_096_0243_0013, g32p_row04_traceSegment_096_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 216 27 27, g32p_row04_traceSegment_096_0216_0027, g32p_row04_traceSegment_096_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 270 13 14, g32p_row04_traceSegment_096_0270_0013, g32p_row04_traceSegment_096_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 297 13 14, g32p_row04_traceSegment_096_0297_0013, g32p_row04_traceSegment_096_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 270 27 27, g32p_row04_traceSegment_096_0270_0027, g32p_row04_traceSegment_096_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 216 54 54, g32p_row04_traceSegment_096_0216_0054, g32p_row04_traceSegment_096_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 324 13 14, g32p_row04_traceSegment_096_0324_0013, g32p_row04_traceSegment_096_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 351 13 14, g32p_row04_traceSegment_096_0351_0013, g32p_row04_traceSegment_096_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 324 27 27, g32p_row04_traceSegment_096_0324_0027, g32p_row04_traceSegment_096_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 378 13 14, g32p_row04_traceSegment_096_0378_0013, g32p_row04_traceSegment_096_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 405 13 14, g32p_row04_traceSegment_096_0405_0013, g32p_row04_traceSegment_096_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 378 27 27, g32p_row04_traceSegment_096_0378_0027, g32p_row04_traceSegment_096_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 324 54 54, g32p_row04_traceSegment_096_0324_0054, g32p_row04_traceSegment_096_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 216 108 108, g32p_row04_traceSegment_096_0216_0108, g32p_row04_traceSegment_096_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_096 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 0 216 216, g32p_row04_traceSegment_096_0000_0216, g32p_row04_traceSegment_096_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 432 13 14, g32p_row04_traceSegment_096_0432_0013, g32p_row04_traceSegment_096_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 459 13 14, g32p_row04_traceSegment_096_0459_0013, g32p_row04_traceSegment_096_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 432 27 27, g32p_row04_traceSegment_096_0432_0027, g32p_row04_traceSegment_096_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 499 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 486 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 486 13 14, g32p_row04_traceSegment_096_0486_0013, g32p_row04_traceSegment_096_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 513 13 14, g32p_row04_traceSegment_096_0513_0013, g32p_row04_traceSegment_096_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 486 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 486 27 27, g32p_row04_traceSegment_096_0486_0027, g32p_row04_traceSegment_096_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 432 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 432 54 54, g32p_row04_traceSegment_096_0432_0054, g32p_row04_traceSegment_096_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 540 13 14, g32p_row04_traceSegment_096_0540_0013, g32p_row04_traceSegment_096_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 567 13 14, g32p_row04_traceSegment_096_0567_0013, g32p_row04_traceSegment_096_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 540 27 27, g32p_row04_traceSegment_096_0540_0027, g32p_row04_traceSegment_096_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 594 13 14, g32p_row04_traceSegment_096_0594_0013, g32p_row04_traceSegment_096_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 621 13 14, g32p_row04_traceSegment_096_0621_0013, g32p_row04_traceSegment_096_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 594 27 27, g32p_row04_traceSegment_096_0594_0027, g32p_row04_traceSegment_096_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 540 54 54, g32p_row04_traceSegment_096_0540_0054, g32p_row04_traceSegment_096_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 432 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 432 108 108, g32p_row04_traceSegment_096_0432_0108, g32p_row04_traceSegment_096_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 648 13 14, g32p_row04_traceSegment_096_0648_0013, g32p_row04_traceSegment_096_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 675 13 14, g32p_row04_traceSegment_096_0675_0013, g32p_row04_traceSegment_096_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 648 27 27, g32p_row04_traceSegment_096_0648_0027, g32p_row04_traceSegment_096_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 702 13 14, g32p_row04_traceSegment_096_0702_0013, g32p_row04_traceSegment_096_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 729 13 14, g32p_row04_traceSegment_096_0729_0013, g32p_row04_traceSegment_096_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 702 27 27, g32p_row04_traceSegment_096_0702_0027, g32p_row04_traceSegment_096_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 648 54 54, g32p_row04_traceSegment_096_0648_0054, g32p_row04_traceSegment_096_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 756 13 14, g32p_row04_traceSegment_096_0756_0013, g32p_row04_traceSegment_096_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 783 13 14, g32p_row04_traceSegment_096_0783_0013, g32p_row04_traceSegment_096_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 756 27 27, g32p_row04_traceSegment_096_0756_0027, g32p_row04_traceSegment_096_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 810 13 14, g32p_row04_traceSegment_096_0810_0013, g32p_row04_traceSegment_096_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 837 13 14, g32p_row04_traceSegment_096_0837_0013, g32p_row04_traceSegment_096_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 810 27 27, g32p_row04_traceSegment_096_0810_0027, g32p_row04_traceSegment_096_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 756 54 54, g32p_row04_traceSegment_096_0756_0054, g32p_row04_traceSegment_096_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 648 108 108, g32p_row04_traceSegment_096_0648_0108, g32p_row04_traceSegment_096_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_096 432 432 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 432 216 216, g32p_row04_traceSegment_096_0432_0216, g32p_row04_traceSegment_096_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_096 0 864 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 0 432 432, g32p_row04_traceSegment_096_0000_0432, g32p_row04_traceSegment_096_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 864 13 14, g32p_row04_traceSegment_096_0864_0013, g32p_row04_traceSegment_096_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 891 13 14, g32p_row04_traceSegment_096_0891_0013, g32p_row04_traceSegment_096_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 864 27 27, g32p_row04_traceSegment_096_0864_0027, g32p_row04_traceSegment_096_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 918 13 14, g32p_row04_traceSegment_096_0918_0013, g32p_row04_traceSegment_096_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 945 13 14, g32p_row04_traceSegment_096_0945_0013, g32p_row04_traceSegment_096_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 918 27 27, g32p_row04_traceSegment_096_0918_0027, g32p_row04_traceSegment_096_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 864 54 54, g32p_row04_traceSegment_096_0864_0054, g32p_row04_traceSegment_096_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 972 13 14, g32p_row04_traceSegment_096_0972_0013, g32p_row04_traceSegment_096_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 999 13 14, g32p_row04_traceSegment_096_0999_0013, g32p_row04_traceSegment_096_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 972 27 27, g32p_row04_traceSegment_096_0972_0027, g32p_row04_traceSegment_096_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1026 13 14, g32p_row04_traceSegment_096_1026_0013, g32p_row04_traceSegment_096_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1053 13 14, g32p_row04_traceSegment_096_1053_0013, g32p_row04_traceSegment_096_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1026 27 27, g32p_row04_traceSegment_096_1026_0027, g32p_row04_traceSegment_096_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 972 54 54, g32p_row04_traceSegment_096_0972_0054, g32p_row04_traceSegment_096_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 864 108 108, g32p_row04_traceSegment_096_0864_0108, g32p_row04_traceSegment_096_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1080 13 14, g32p_row04_traceSegment_096_1080_0013, g32p_row04_traceSegment_096_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1107 13 14, g32p_row04_traceSegment_096_1107_0013, g32p_row04_traceSegment_096_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1080 27 27, g32p_row04_traceSegment_096_1080_0027, g32p_row04_traceSegment_096_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1134 13 14, g32p_row04_traceSegment_096_1134_0013, g32p_row04_traceSegment_096_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1161 13 14, g32p_row04_traceSegment_096_1161_0013, g32p_row04_traceSegment_096_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1134 27 27, g32p_row04_traceSegment_096_1134_0027, g32p_row04_traceSegment_096_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1080 54 54, g32p_row04_traceSegment_096_1080_0054, g32p_row04_traceSegment_096_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1188 13 14, g32p_row04_traceSegment_096_1188_0013, g32p_row04_traceSegment_096_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1215 13 14, g32p_row04_traceSegment_096_1215_0013, g32p_row04_traceSegment_096_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1188 27 27, g32p_row04_traceSegment_096_1188_0027, g32p_row04_traceSegment_096_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1242 13 14, g32p_row04_traceSegment_096_1242_0013, g32p_row04_traceSegment_096_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1269 13 14, g32p_row04_traceSegment_096_1269_0013, g32p_row04_traceSegment_096_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1242 27 27, g32p_row04_traceSegment_096_1242_0027, g32p_row04_traceSegment_096_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1188 54 54, g32p_row04_traceSegment_096_1188_0054, g32p_row04_traceSegment_096_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1080 108 108, g32p_row04_traceSegment_096_1080_0108, g32p_row04_traceSegment_096_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_096 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 864 216 216, g32p_row04_traceSegment_096_0864_0216, g32p_row04_traceSegment_096_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1296 13 14, g32p_row04_traceSegment_096_1296_0013, g32p_row04_traceSegment_096_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1323 13 14, g32p_row04_traceSegment_096_1323_0013, g32p_row04_traceSegment_096_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1296 27 27, g32p_row04_traceSegment_096_1296_0027, g32p_row04_traceSegment_096_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1350 13 14, g32p_row04_traceSegment_096_1350_0013, g32p_row04_traceSegment_096_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1377 13 14, g32p_row04_traceSegment_096_1377_0013, g32p_row04_traceSegment_096_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1350 27 27, g32p_row04_traceSegment_096_1350_0027, g32p_row04_traceSegment_096_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1296 54 54, g32p_row04_traceSegment_096_1296_0054, g32p_row04_traceSegment_096_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1404 13 14, g32p_row04_traceSegment_096_1404_0013, g32p_row04_traceSegment_096_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1431 13 14, g32p_row04_traceSegment_096_1431_0013, g32p_row04_traceSegment_096_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1404 27 27, g32p_row04_traceSegment_096_1404_0027, g32p_row04_traceSegment_096_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1458 13 14, g32p_row04_traceSegment_096_1458_0013, g32p_row04_traceSegment_096_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1485 13 14, g32p_row04_traceSegment_096_1485_0013, g32p_row04_traceSegment_096_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1458 27 27, g32p_row04_traceSegment_096_1458_0027, g32p_row04_traceSegment_096_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1404 54 54, g32p_row04_traceSegment_096_1404_0054, g32p_row04_traceSegment_096_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1296 108 108, g32p_row04_traceSegment_096_1296_0108, g32p_row04_traceSegment_096_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1512 13 14, g32p_row04_traceSegment_096_1512_0013, g32p_row04_traceSegment_096_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1539 13 14, g32p_row04_traceSegment_096_1539_0013, g32p_row04_traceSegment_096_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1512 27 27, g32p_row04_traceSegment_096_1512_0027, g32p_row04_traceSegment_096_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1566 13 14, g32p_row04_traceSegment_096_1566_0013, g32p_row04_traceSegment_096_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1593 13 14, g32p_row04_traceSegment_096_1593_0013, g32p_row04_traceSegment_096_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1566 27 27, g32p_row04_traceSegment_096_1566_0027, g32p_row04_traceSegment_096_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1512 54 54, g32p_row04_traceSegment_096_1512_0054, g32p_row04_traceSegment_096_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1620 13 14, g32p_row04_traceSegment_096_1620_0013, g32p_row04_traceSegment_096_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1647 13 14, g32p_row04_traceSegment_096_1647_0013, g32p_row04_traceSegment_096_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1620 27 27, g32p_row04_traceSegment_096_1620_0027, g32p_row04_traceSegment_096_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1674 13 14, g32p_row04_traceSegment_096_1674_0013, g32p_row04_traceSegment_096_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_096 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_096 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_096_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_096 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1701 13 14, g32p_row04_traceSegment_096_1701_0013, g32p_row04_traceSegment_096_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_096 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1674 27 27, g32p_row04_traceSegment_096_1674_0027, g32p_row04_traceSegment_096_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_096 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1620 54 54, g32p_row04_traceSegment_096_1620_0054, g32p_row04_traceSegment_096_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_096 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1512 108 108, g32p_row04_traceSegment_096_1512_0108, g32p_row04_traceSegment_096_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_096_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_096 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 1296 216 216, g32p_row04_traceSegment_096_1296_0216, g32p_row04_traceSegment_096_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_096 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 864 432 432, g32p_row04_traceSegment_096_0864_0432, g32p_row04_traceSegment_096_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_096_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_096 0 1728 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_096 0 864 864, g32p_row04_traceSegment_096_0000_0864, g32p_row04_traceSegment_096_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_096 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 96 = [0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_096_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_097 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 97 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_097_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 0 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 0 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 0 13 14, g32p_row04_traceSegment_097_0000_0013, g32p_row04_traceSegment_097_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 27 13 14, g32p_row04_traceSegment_097_0027_0013, g32p_row04_traceSegment_097_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 0 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 0 27 27, g32p_row04_traceSegment_097_0000_0027, g32p_row04_traceSegment_097_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 54 13 14, g32p_row04_traceSegment_097_0054_0013, g32p_row04_traceSegment_097_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 81 13 14, g32p_row04_traceSegment_097_0081_0013, g32p_row04_traceSegment_097_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 54 27 27, g32p_row04_traceSegment_097_0054_0027, g32p_row04_traceSegment_097_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 0 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 0 54 54, g32p_row04_traceSegment_097_0000_0054, g32p_row04_traceSegment_097_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 108 13 14, g32p_row04_traceSegment_097_0108_0013, g32p_row04_traceSegment_097_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 135 13 14, g32p_row04_traceSegment_097_0135_0013, g32p_row04_traceSegment_097_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 108 27 27, g32p_row04_traceSegment_097_0108_0027, g32p_row04_traceSegment_097_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 162 13 14, g32p_row04_traceSegment_097_0162_0013, g32p_row04_traceSegment_097_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 189 13 14, g32p_row04_traceSegment_097_0189_0013, g32p_row04_traceSegment_097_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 162 27 27, g32p_row04_traceSegment_097_0162_0027, g32p_row04_traceSegment_097_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 108 54 54, g32p_row04_traceSegment_097_0108_0054, g32p_row04_traceSegment_097_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 0 216 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 0 108 108, g32p_row04_traceSegment_097_0000_0108, g32p_row04_traceSegment_097_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 216 13 14, g32p_row04_traceSegment_097_0216_0013, g32p_row04_traceSegment_097_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 243 13 14, g32p_row04_traceSegment_097_0243_0013, g32p_row04_traceSegment_097_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 216 27 27, g32p_row04_traceSegment_097_0216_0027, g32p_row04_traceSegment_097_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 270 13 14, g32p_row04_traceSegment_097_0270_0013, g32p_row04_traceSegment_097_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 297 13 14, g32p_row04_traceSegment_097_0297_0013, g32p_row04_traceSegment_097_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 270 27 27, g32p_row04_traceSegment_097_0270_0027, g32p_row04_traceSegment_097_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 216 54 54, g32p_row04_traceSegment_097_0216_0054, g32p_row04_traceSegment_097_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 324 13 14, g32p_row04_traceSegment_097_0324_0013, g32p_row04_traceSegment_097_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 351 13 14, g32p_row04_traceSegment_097_0351_0013, g32p_row04_traceSegment_097_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 324 27 27, g32p_row04_traceSegment_097_0324_0027, g32p_row04_traceSegment_097_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 378 13 14, g32p_row04_traceSegment_097_0378_0013, g32p_row04_traceSegment_097_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 405 13 14, g32p_row04_traceSegment_097_0405_0013, g32p_row04_traceSegment_097_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 378 27 27, g32p_row04_traceSegment_097_0378_0027, g32p_row04_traceSegment_097_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 324 54 54, g32p_row04_traceSegment_097_0324_0054, g32p_row04_traceSegment_097_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 216 108 108, g32p_row04_traceSegment_097_0216_0108, g32p_row04_traceSegment_097_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_097 0 432 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 0 216 216, g32p_row04_traceSegment_097_0000_0216, g32p_row04_traceSegment_097_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 432 13 14, g32p_row04_traceSegment_097_0432_0013, g32p_row04_traceSegment_097_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 459 13 14, g32p_row04_traceSegment_097_0459_0013, g32p_row04_traceSegment_097_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 432 27 27, g32p_row04_traceSegment_097_0432_0027, g32p_row04_traceSegment_097_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 486 13 14, g32p_row04_traceSegment_097_0486_0013, g32p_row04_traceSegment_097_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 513 13 14, g32p_row04_traceSegment_097_0513_0013, g32p_row04_traceSegment_097_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 486 27 27, g32p_row04_traceSegment_097_0486_0027, g32p_row04_traceSegment_097_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 432 54 54, g32p_row04_traceSegment_097_0432_0054, g32p_row04_traceSegment_097_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 540 13 14, g32p_row04_traceSegment_097_0540_0013, g32p_row04_traceSegment_097_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 567 13 14, g32p_row04_traceSegment_097_0567_0013, g32p_row04_traceSegment_097_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 540 27 27, g32p_row04_traceSegment_097_0540_0027, g32p_row04_traceSegment_097_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 594 13 14, g32p_row04_traceSegment_097_0594_0013, g32p_row04_traceSegment_097_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 621 13 14, g32p_row04_traceSegment_097_0621_0013, g32p_row04_traceSegment_097_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 594 27 27, g32p_row04_traceSegment_097_0594_0027, g32p_row04_traceSegment_097_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 540 54 54, g32p_row04_traceSegment_097_0540_0054, g32p_row04_traceSegment_097_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 432 108 108, g32p_row04_traceSegment_097_0432_0108, g32p_row04_traceSegment_097_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 648 13 14, g32p_row04_traceSegment_097_0648_0013, g32p_row04_traceSegment_097_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 675 13 14, g32p_row04_traceSegment_097_0675_0013, g32p_row04_traceSegment_097_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 648 27 27, g32p_row04_traceSegment_097_0648_0027, g32p_row04_traceSegment_097_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 702 13 14, g32p_row04_traceSegment_097_0702_0013, g32p_row04_traceSegment_097_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 729 13 14, g32p_row04_traceSegment_097_0729_0013, g32p_row04_traceSegment_097_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 702 27 27, g32p_row04_traceSegment_097_0702_0027, g32p_row04_traceSegment_097_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 648 54 54, g32p_row04_traceSegment_097_0648_0054, g32p_row04_traceSegment_097_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 756 13 14, g32p_row04_traceSegment_097_0756_0013, g32p_row04_traceSegment_097_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 783 13 14, g32p_row04_traceSegment_097_0783_0013, g32p_row04_traceSegment_097_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 756 27 27, g32p_row04_traceSegment_097_0756_0027, g32p_row04_traceSegment_097_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 810 13 14, g32p_row04_traceSegment_097_0810_0013, g32p_row04_traceSegment_097_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 837 13 14, g32p_row04_traceSegment_097_0837_0013, g32p_row04_traceSegment_097_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 810 27 27, g32p_row04_traceSegment_097_0810_0027, g32p_row04_traceSegment_097_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 756 54 54, g32p_row04_traceSegment_097_0756_0054, g32p_row04_traceSegment_097_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 648 108 108, g32p_row04_traceSegment_097_0648_0108, g32p_row04_traceSegment_097_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_097 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 432 216 216, g32p_row04_traceSegment_097_0432_0216, g32p_row04_traceSegment_097_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_097 0 864 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 0 432 432, g32p_row04_traceSegment_097_0000_0432, g32p_row04_traceSegment_097_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 864 13 14, g32p_row04_traceSegment_097_0864_0013, g32p_row04_traceSegment_097_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 891 13 14, g32p_row04_traceSegment_097_0891_0013, g32p_row04_traceSegment_097_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 864 27 27, g32p_row04_traceSegment_097_0864_0027, g32p_row04_traceSegment_097_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 918 13 14, g32p_row04_traceSegment_097_0918_0013, g32p_row04_traceSegment_097_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 945 13 14, g32p_row04_traceSegment_097_0945_0013, g32p_row04_traceSegment_097_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 918 27 27, g32p_row04_traceSegment_097_0918_0027, g32p_row04_traceSegment_097_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 864 54 54, g32p_row04_traceSegment_097_0864_0054, g32p_row04_traceSegment_097_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 972 13 14, g32p_row04_traceSegment_097_0972_0013, g32p_row04_traceSegment_097_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 999 13 14, g32p_row04_traceSegment_097_0999_0013, g32p_row04_traceSegment_097_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 972 27 27, g32p_row04_traceSegment_097_0972_0027, g32p_row04_traceSegment_097_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1026 13 14, g32p_row04_traceSegment_097_1026_0013, g32p_row04_traceSegment_097_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1053 13 14, g32p_row04_traceSegment_097_1053_0013, g32p_row04_traceSegment_097_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1026 27 27, g32p_row04_traceSegment_097_1026_0027, g32p_row04_traceSegment_097_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 972 54 54, g32p_row04_traceSegment_097_0972_0054, g32p_row04_traceSegment_097_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 864 108 108, g32p_row04_traceSegment_097_0864_0108, g32p_row04_traceSegment_097_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1080 13 14, g32p_row04_traceSegment_097_1080_0013, g32p_row04_traceSegment_097_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1107 13 14, g32p_row04_traceSegment_097_1107_0013, g32p_row04_traceSegment_097_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1080 27 27, g32p_row04_traceSegment_097_1080_0027, g32p_row04_traceSegment_097_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1134 13 14, g32p_row04_traceSegment_097_1134_0013, g32p_row04_traceSegment_097_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1161 13 14, g32p_row04_traceSegment_097_1161_0013, g32p_row04_traceSegment_097_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1134 27 27, g32p_row04_traceSegment_097_1134_0027, g32p_row04_traceSegment_097_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1080 54 54, g32p_row04_traceSegment_097_1080_0054, g32p_row04_traceSegment_097_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1188 13 14, g32p_row04_traceSegment_097_1188_0013, g32p_row04_traceSegment_097_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1215 13 14, g32p_row04_traceSegment_097_1215_0013, g32p_row04_traceSegment_097_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1188 27 27, g32p_row04_traceSegment_097_1188_0027, g32p_row04_traceSegment_097_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1242 13 14, g32p_row04_traceSegment_097_1242_0013, g32p_row04_traceSegment_097_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1269 13 14, g32p_row04_traceSegment_097_1269_0013, g32p_row04_traceSegment_097_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1242 27 27, g32p_row04_traceSegment_097_1242_0027, g32p_row04_traceSegment_097_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1188 54 54, g32p_row04_traceSegment_097_1188_0054, g32p_row04_traceSegment_097_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1080 108 108, g32p_row04_traceSegment_097_1080_0108, g32p_row04_traceSegment_097_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_097 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 864 216 216, g32p_row04_traceSegment_097_0864_0216, g32p_row04_traceSegment_097_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1296 13 14, g32p_row04_traceSegment_097_1296_0013, g32p_row04_traceSegment_097_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1323 13 14, g32p_row04_traceSegment_097_1323_0013, g32p_row04_traceSegment_097_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1296 27 27, g32p_row04_traceSegment_097_1296_0027, g32p_row04_traceSegment_097_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1350 13 14, g32p_row04_traceSegment_097_1350_0013, g32p_row04_traceSegment_097_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1377 13 14, g32p_row04_traceSegment_097_1377_0013, g32p_row04_traceSegment_097_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1350 27 27, g32p_row04_traceSegment_097_1350_0027, g32p_row04_traceSegment_097_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1296 54 54, g32p_row04_traceSegment_097_1296_0054, g32p_row04_traceSegment_097_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1404 13 14, g32p_row04_traceSegment_097_1404_0013, g32p_row04_traceSegment_097_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1431 13 14, g32p_row04_traceSegment_097_1431_0013, g32p_row04_traceSegment_097_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1404 27 27, g32p_row04_traceSegment_097_1404_0027, g32p_row04_traceSegment_097_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1458 13 14, g32p_row04_traceSegment_097_1458_0013, g32p_row04_traceSegment_097_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1485 13 14, g32p_row04_traceSegment_097_1485_0013, g32p_row04_traceSegment_097_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1458 27 27, g32p_row04_traceSegment_097_1458_0027, g32p_row04_traceSegment_097_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1404 54 54, g32p_row04_traceSegment_097_1404_0054, g32p_row04_traceSegment_097_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1296 108 108, g32p_row04_traceSegment_097_1296_0108, g32p_row04_traceSegment_097_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1512 13 14, g32p_row04_traceSegment_097_1512_0013, g32p_row04_traceSegment_097_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1539 13 14, g32p_row04_traceSegment_097_1539_0013, g32p_row04_traceSegment_097_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1512 27 27, g32p_row04_traceSegment_097_1512_0027, g32p_row04_traceSegment_097_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1566 13 14, g32p_row04_traceSegment_097_1566_0013, g32p_row04_traceSegment_097_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1593 13 14, g32p_row04_traceSegment_097_1593_0013, g32p_row04_traceSegment_097_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1566 27 27, g32p_row04_traceSegment_097_1566_0027, g32p_row04_traceSegment_097_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1512 54 54, g32p_row04_traceSegment_097_1512_0054, g32p_row04_traceSegment_097_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1620 13 14, g32p_row04_traceSegment_097_1620_0013, g32p_row04_traceSegment_097_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1647 13 14, g32p_row04_traceSegment_097_1647_0013, g32p_row04_traceSegment_097_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1620 27 27, g32p_row04_traceSegment_097_1620_0027, g32p_row04_traceSegment_097_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1674 13 14, g32p_row04_traceSegment_097_1674_0013, g32p_row04_traceSegment_097_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_097 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_097 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_097_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_097 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1701 13 14, g32p_row04_traceSegment_097_1701_0013, g32p_row04_traceSegment_097_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_097 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1674 27 27, g32p_row04_traceSegment_097_1674_0027, g32p_row04_traceSegment_097_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_097 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1620 54 54, g32p_row04_traceSegment_097_1620_0054, g32p_row04_traceSegment_097_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_097 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1512 108 108, g32p_row04_traceSegment_097_1512_0108, g32p_row04_traceSegment_097_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_097_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_097 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 1296 216 216, g32p_row04_traceSegment_097_1296_0216, g32p_row04_traceSegment_097_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_097 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 864 432 432, g32p_row04_traceSegment_097_0864_0432, g32p_row04_traceSegment_097_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_097_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_097 0 1728 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_097 0 864 864, g32p_row04_traceSegment_097_0000_0864, g32p_row04_traceSegment_097_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_097 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 97 = [0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_097_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_098 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 98 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_098_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 0 13 14, g32p_row04_traceSegment_098_0000_0013, g32p_row04_traceSegment_098_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 27 13 14, g32p_row04_traceSegment_098_0027_0013, g32p_row04_traceSegment_098_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 0 27 27, g32p_row04_traceSegment_098_0000_0027, g32p_row04_traceSegment_098_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 54 13 14, g32p_row04_traceSegment_098_0054_0013, g32p_row04_traceSegment_098_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 81 13 14, g32p_row04_traceSegment_098_0081_0013, g32p_row04_traceSegment_098_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 54 27 27, g32p_row04_traceSegment_098_0054_0027, g32p_row04_traceSegment_098_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 0 54 54, g32p_row04_traceSegment_098_0000_0054, g32p_row04_traceSegment_098_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 108 13 14, g32p_row04_traceSegment_098_0108_0013, g32p_row04_traceSegment_098_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 148 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 135 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 135 13 14, g32p_row04_traceSegment_098_0135_0013, g32p_row04_traceSegment_098_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 108 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 108 27 27, g32p_row04_traceSegment_098_0108_0027, g32p_row04_traceSegment_098_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 175 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 162 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 162 13 14, g32p_row04_traceSegment_098_0162_0013, g32p_row04_traceSegment_098_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 189 13 14, g32p_row04_traceSegment_098_0189_0013, g32p_row04_traceSegment_098_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 162 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 162 27 27, g32p_row04_traceSegment_098_0162_0027, g32p_row04_traceSegment_098_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 108 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 108 54 54, g32p_row04_traceSegment_098_0108_0054, g32p_row04_traceSegment_098_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 0 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 0 108 108, g32p_row04_traceSegment_098_0000_0108, g32p_row04_traceSegment_098_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 216 13 14, g32p_row04_traceSegment_098_0216_0013, g32p_row04_traceSegment_098_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 243 13 14, g32p_row04_traceSegment_098_0243_0013, g32p_row04_traceSegment_098_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 216 27 27, g32p_row04_traceSegment_098_0216_0027, g32p_row04_traceSegment_098_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 270 13 14, g32p_row04_traceSegment_098_0270_0013, g32p_row04_traceSegment_098_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 297 13 14, g32p_row04_traceSegment_098_0297_0013, g32p_row04_traceSegment_098_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 270 27 27, g32p_row04_traceSegment_098_0270_0027, g32p_row04_traceSegment_098_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 216 54 54, g32p_row04_traceSegment_098_0216_0054, g32p_row04_traceSegment_098_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 324 13 14, g32p_row04_traceSegment_098_0324_0013, g32p_row04_traceSegment_098_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 351 13 14, g32p_row04_traceSegment_098_0351_0013, g32p_row04_traceSegment_098_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 324 27 27, g32p_row04_traceSegment_098_0324_0027, g32p_row04_traceSegment_098_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 378 13 14, g32p_row04_traceSegment_098_0378_0013, g32p_row04_traceSegment_098_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 405 13 14, g32p_row04_traceSegment_098_0405_0013, g32p_row04_traceSegment_098_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 378 27 27, g32p_row04_traceSegment_098_0378_0027, g32p_row04_traceSegment_098_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 324 54 54, g32p_row04_traceSegment_098_0324_0054, g32p_row04_traceSegment_098_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 216 108 108, g32p_row04_traceSegment_098_0216_0108, g32p_row04_traceSegment_098_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_098 0 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 0 216 216, g32p_row04_traceSegment_098_0000_0216, g32p_row04_traceSegment_098_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 432 13 14, g32p_row04_traceSegment_098_0432_0013, g32p_row04_traceSegment_098_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 459 13 14, g32p_row04_traceSegment_098_0459_0013, g32p_row04_traceSegment_098_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 432 27 27, g32p_row04_traceSegment_098_0432_0027, g32p_row04_traceSegment_098_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 486 13 14, g32p_row04_traceSegment_098_0486_0013, g32p_row04_traceSegment_098_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 513 13 14, g32p_row04_traceSegment_098_0513_0013, g32p_row04_traceSegment_098_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 486 27 27, g32p_row04_traceSegment_098_0486_0027, g32p_row04_traceSegment_098_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 432 54 54, g32p_row04_traceSegment_098_0432_0054, g32p_row04_traceSegment_098_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 540 13 14, g32p_row04_traceSegment_098_0540_0013, g32p_row04_traceSegment_098_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 567 13 14, g32p_row04_traceSegment_098_0567_0013, g32p_row04_traceSegment_098_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 540 27 27, g32p_row04_traceSegment_098_0540_0027, g32p_row04_traceSegment_098_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 594 13 14, g32p_row04_traceSegment_098_0594_0013, g32p_row04_traceSegment_098_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 621 13 14, g32p_row04_traceSegment_098_0621_0013, g32p_row04_traceSegment_098_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 594 27 27, g32p_row04_traceSegment_098_0594_0027, g32p_row04_traceSegment_098_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 540 54 54, g32p_row04_traceSegment_098_0540_0054, g32p_row04_traceSegment_098_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 432 108 108, g32p_row04_traceSegment_098_0432_0108, g32p_row04_traceSegment_098_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 648 13 14, g32p_row04_traceSegment_098_0648_0013, g32p_row04_traceSegment_098_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 675 13 14, g32p_row04_traceSegment_098_0675_0013, g32p_row04_traceSegment_098_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 648 27 27, g32p_row04_traceSegment_098_0648_0027, g32p_row04_traceSegment_098_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 702 13 14, g32p_row04_traceSegment_098_0702_0013, g32p_row04_traceSegment_098_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 729 13 14, g32p_row04_traceSegment_098_0729_0013, g32p_row04_traceSegment_098_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 702 27 27, g32p_row04_traceSegment_098_0702_0027, g32p_row04_traceSegment_098_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 648 54 54, g32p_row04_traceSegment_098_0648_0054, g32p_row04_traceSegment_098_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 756 13 14, g32p_row04_traceSegment_098_0756_0013, g32p_row04_traceSegment_098_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 783 13 14, g32p_row04_traceSegment_098_0783_0013, g32p_row04_traceSegment_098_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 756 27 27, g32p_row04_traceSegment_098_0756_0027, g32p_row04_traceSegment_098_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 810 13 14, g32p_row04_traceSegment_098_0810_0013, g32p_row04_traceSegment_098_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 837 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 850 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 837 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 837 13 14, g32p_row04_traceSegment_098_0837_0013, g32p_row04_traceSegment_098_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 810 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 810 27 27, g32p_row04_traceSegment_098_0810_0027, g32p_row04_traceSegment_098_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 756 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 756 54 54, g32p_row04_traceSegment_098_0756_0054, g32p_row04_traceSegment_098_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 648 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 648 108 108, g32p_row04_traceSegment_098_0648_0108, g32p_row04_traceSegment_098_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_098 432 432 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 432 216 216, g32p_row04_traceSegment_098_0432_0216, g32p_row04_traceSegment_098_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_098 0 864 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 0 432 432, g32p_row04_traceSegment_098_0000_0432, g32p_row04_traceSegment_098_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 877 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 864 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 864 13 14, g32p_row04_traceSegment_098_0864_0013, g32p_row04_traceSegment_098_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 891 13 14, g32p_row04_traceSegment_098_0891_0013, g32p_row04_traceSegment_098_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 864 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 864 27 27, g32p_row04_traceSegment_098_0864_0027, g32p_row04_traceSegment_098_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 931 14 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 918 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 918 13 14, g32p_row04_traceSegment_098_0918_0013, g32p_row04_traceSegment_098_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 945 13 14, g32p_row04_traceSegment_098_0945_0013, g32p_row04_traceSegment_098_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 918 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 918 27 27, g32p_row04_traceSegment_098_0918_0027, g32p_row04_traceSegment_098_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 864 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 864 54 54, g32p_row04_traceSegment_098_0864_0054, g32p_row04_traceSegment_098_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 972 13 14, g32p_row04_traceSegment_098_0972_0013, g32p_row04_traceSegment_098_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 999 13 14, g32p_row04_traceSegment_098_0999_0013, g32p_row04_traceSegment_098_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 972 27 27, g32p_row04_traceSegment_098_0972_0027, g32p_row04_traceSegment_098_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1039 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1026 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1026 13 14, g32p_row04_traceSegment_098_1026_0013, g32p_row04_traceSegment_098_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1066 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1053 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1053 13 14, g32p_row04_traceSegment_098_1053_0013, g32p_row04_traceSegment_098_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1026 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1026 27 27, g32p_row04_traceSegment_098_1026_0027, g32p_row04_traceSegment_098_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 972 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 972 54 54, g32p_row04_traceSegment_098_0972_0054, g32p_row04_traceSegment_098_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 864 216 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 864 108 108, g32p_row04_traceSegment_098_0864_0108, g32p_row04_traceSegment_098_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1080 13 14, g32p_row04_traceSegment_098_1080_0013, g32p_row04_traceSegment_098_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1107 13 14, g32p_row04_traceSegment_098_1107_0013, g32p_row04_traceSegment_098_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1080 27 27, g32p_row04_traceSegment_098_1080_0027, g32p_row04_traceSegment_098_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1134 13 14, g32p_row04_traceSegment_098_1134_0013, g32p_row04_traceSegment_098_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1161 13 14, g32p_row04_traceSegment_098_1161_0013, g32p_row04_traceSegment_098_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1134 27 27, g32p_row04_traceSegment_098_1134_0027, g32p_row04_traceSegment_098_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1080 54 54, g32p_row04_traceSegment_098_1080_0054, g32p_row04_traceSegment_098_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1188 13 14, g32p_row04_traceSegment_098_1188_0013, g32p_row04_traceSegment_098_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1215 13 14, g32p_row04_traceSegment_098_1215_0013, g32p_row04_traceSegment_098_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1188 27 27, g32p_row04_traceSegment_098_1188_0027, g32p_row04_traceSegment_098_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1242 13 14, g32p_row04_traceSegment_098_1242_0013, g32p_row04_traceSegment_098_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1269 13 14, g32p_row04_traceSegment_098_1269_0013, g32p_row04_traceSegment_098_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1242 27 27, g32p_row04_traceSegment_098_1242_0027, g32p_row04_traceSegment_098_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1188 54 54, g32p_row04_traceSegment_098_1188_0054, g32p_row04_traceSegment_098_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1080 108 108, g32p_row04_traceSegment_098_1080_0108, g32p_row04_traceSegment_098_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_098 864 432 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 864 216 216, g32p_row04_traceSegment_098_0864_0216, g32p_row04_traceSegment_098_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1296 13 14, g32p_row04_traceSegment_098_1296_0013, g32p_row04_traceSegment_098_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1323 13 14, g32p_row04_traceSegment_098_1323_0013, g32p_row04_traceSegment_098_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1296 27 27, g32p_row04_traceSegment_098_1296_0027, g32p_row04_traceSegment_098_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1350 13 14, g32p_row04_traceSegment_098_1350_0013, g32p_row04_traceSegment_098_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1377 13 14, g32p_row04_traceSegment_098_1377_0013, g32p_row04_traceSegment_098_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1350 27 27, g32p_row04_traceSegment_098_1350_0027, g32p_row04_traceSegment_098_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1296 54 54, g32p_row04_traceSegment_098_1296_0054, g32p_row04_traceSegment_098_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1404 13 14, g32p_row04_traceSegment_098_1404_0013, g32p_row04_traceSegment_098_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1431 13 14, g32p_row04_traceSegment_098_1431_0013, g32p_row04_traceSegment_098_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1404 27 27, g32p_row04_traceSegment_098_1404_0027, g32p_row04_traceSegment_098_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1458 13 14, g32p_row04_traceSegment_098_1458_0013, g32p_row04_traceSegment_098_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1485 13 14, g32p_row04_traceSegment_098_1485_0013, g32p_row04_traceSegment_098_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1458 27 27, g32p_row04_traceSegment_098_1458_0027, g32p_row04_traceSegment_098_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1404 54 54, g32p_row04_traceSegment_098_1404_0054, g32p_row04_traceSegment_098_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1296 108 108, g32p_row04_traceSegment_098_1296_0108, g32p_row04_traceSegment_098_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1512 13 14, g32p_row04_traceSegment_098_1512_0013, g32p_row04_traceSegment_098_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1539 13 14, g32p_row04_traceSegment_098_1539_0013, g32p_row04_traceSegment_098_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1512 27 27, g32p_row04_traceSegment_098_1512_0027, g32p_row04_traceSegment_098_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1566 13 14, g32p_row04_traceSegment_098_1566_0013, g32p_row04_traceSegment_098_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1593 13 14, g32p_row04_traceSegment_098_1593_0013, g32p_row04_traceSegment_098_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1566 27 27, g32p_row04_traceSegment_098_1566_0027, g32p_row04_traceSegment_098_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1512 54 54, g32p_row04_traceSegment_098_1512_0054, g32p_row04_traceSegment_098_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1620 13 14, g32p_row04_traceSegment_098_1620_0013, g32p_row04_traceSegment_098_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1647 13 14, g32p_row04_traceSegment_098_1647_0013, g32p_row04_traceSegment_098_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1620 27 27, g32p_row04_traceSegment_098_1620_0027, g32p_row04_traceSegment_098_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1674 13 14, g32p_row04_traceSegment_098_1674_0013, g32p_row04_traceSegment_098_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_098 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_098 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_098_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_098 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1701 13 14, g32p_row04_traceSegment_098_1701_0013, g32p_row04_traceSegment_098_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_098 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1674 27 27, g32p_row04_traceSegment_098_1674_0027, g32p_row04_traceSegment_098_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_098 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1620 54 54, g32p_row04_traceSegment_098_1620_0054, g32p_row04_traceSegment_098_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_098 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1512 108 108, g32p_row04_traceSegment_098_1512_0108, g32p_row04_traceSegment_098_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_098_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_098 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 1296 216 216, g32p_row04_traceSegment_098_1296_0216, g32p_row04_traceSegment_098_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_098 864 864 = [2, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 864 432 432, g32p_row04_traceSegment_098_0864_0432, g32p_row04_traceSegment_098_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_098_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_098 0 1728 = [4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_098 0 864 864, g32p_row04_traceSegment_098_0000_0864, g32p_row04_traceSegment_098_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_098 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 98 = [4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_098_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_099 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 99 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_099_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 0 13 14, g32p_row04_traceSegment_099_0000_0013, g32p_row04_traceSegment_099_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 27 13 14, g32p_row04_traceSegment_099_0027_0013, g32p_row04_traceSegment_099_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 0 27 27, g32p_row04_traceSegment_099_0000_0027, g32p_row04_traceSegment_099_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 54 13 14, g32p_row04_traceSegment_099_0054_0013, g32p_row04_traceSegment_099_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 81 13 14, g32p_row04_traceSegment_099_0081_0013, g32p_row04_traceSegment_099_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 54 27 27, g32p_row04_traceSegment_099_0054_0027, g32p_row04_traceSegment_099_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 0 54 54, g32p_row04_traceSegment_099_0000_0054, g32p_row04_traceSegment_099_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 108 13 14, g32p_row04_traceSegment_099_0108_0013, g32p_row04_traceSegment_099_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 135 13 = [1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 135 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 135 13 14, g32p_row04_traceSegment_099_0135_0013, g32p_row04_traceSegment_099_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 108 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 108 27 27, g32p_row04_traceSegment_099_0108_0027, g32p_row04_traceSegment_099_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 162 13 14, g32p_row04_traceSegment_099_0162_0013, g32p_row04_traceSegment_099_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 189 13 14, g32p_row04_traceSegment_099_0189_0013, g32p_row04_traceSegment_099_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 162 27 27, g32p_row04_traceSegment_099_0162_0027, g32p_row04_traceSegment_099_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 108 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 108 54 54, g32p_row04_traceSegment_099_0108_0054, g32p_row04_traceSegment_099_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 0 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 0 108 108, g32p_row04_traceSegment_099_0000_0108, g32p_row04_traceSegment_099_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 216 13 14, g32p_row04_traceSegment_099_0216_0013, g32p_row04_traceSegment_099_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 243 13 14, g32p_row04_traceSegment_099_0243_0013, g32p_row04_traceSegment_099_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 216 27 27, g32p_row04_traceSegment_099_0216_0027, g32p_row04_traceSegment_099_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 283 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 270 13 14, g32p_row04_traceSegment_099_0270_0013, g32p_row04_traceSegment_099_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 297 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 297 13 14, g32p_row04_traceSegment_099_0297_0013, g32p_row04_traceSegment_099_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 270 27 27, g32p_row04_traceSegment_099_0270_0027, g32p_row04_traceSegment_099_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 216 54 54, g32p_row04_traceSegment_099_0216_0054, g32p_row04_traceSegment_099_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 324 13 14, g32p_row04_traceSegment_099_0324_0013, g32p_row04_traceSegment_099_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 351 13 14, g32p_row04_traceSegment_099_0351_0013, g32p_row04_traceSegment_099_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 324 27 27, g32p_row04_traceSegment_099_0324_0027, g32p_row04_traceSegment_099_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 378 13 14, g32p_row04_traceSegment_099_0378_0013, g32p_row04_traceSegment_099_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 405 13 14, g32p_row04_traceSegment_099_0405_0013, g32p_row04_traceSegment_099_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 378 27 27, g32p_row04_traceSegment_099_0378_0027, g32p_row04_traceSegment_099_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 324 54 54, g32p_row04_traceSegment_099_0324_0054, g32p_row04_traceSegment_099_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 216 108 108, g32p_row04_traceSegment_099_0216_0108, g32p_row04_traceSegment_099_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_099 0 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 0 216 216, g32p_row04_traceSegment_099_0000_0216, g32p_row04_traceSegment_099_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 432 13 14, g32p_row04_traceSegment_099_0432_0013, g32p_row04_traceSegment_099_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 459 13 14, g32p_row04_traceSegment_099_0459_0013, g32p_row04_traceSegment_099_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 432 27 27, g32p_row04_traceSegment_099_0432_0027, g32p_row04_traceSegment_099_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 486 13 14, g32p_row04_traceSegment_099_0486_0013, g32p_row04_traceSegment_099_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 513 13 14, g32p_row04_traceSegment_099_0513_0013, g32p_row04_traceSegment_099_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 486 27 27, g32p_row04_traceSegment_099_0486_0027, g32p_row04_traceSegment_099_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 432 54 54, g32p_row04_traceSegment_099_0432_0054, g32p_row04_traceSegment_099_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 540 13 14, g32p_row04_traceSegment_099_0540_0013, g32p_row04_traceSegment_099_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 567 13 14, g32p_row04_traceSegment_099_0567_0013, g32p_row04_traceSegment_099_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 540 27 27, g32p_row04_traceSegment_099_0540_0027, g32p_row04_traceSegment_099_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 594 13 14, g32p_row04_traceSegment_099_0594_0013, g32p_row04_traceSegment_099_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 621 13 14, g32p_row04_traceSegment_099_0621_0013, g32p_row04_traceSegment_099_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 594 27 27, g32p_row04_traceSegment_099_0594_0027, g32p_row04_traceSegment_099_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 540 54 54, g32p_row04_traceSegment_099_0540_0054, g32p_row04_traceSegment_099_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 432 108 108, g32p_row04_traceSegment_099_0432_0108, g32p_row04_traceSegment_099_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 648 13 14, g32p_row04_traceSegment_099_0648_0013, g32p_row04_traceSegment_099_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 675 13 14, g32p_row04_traceSegment_099_0675_0013, g32p_row04_traceSegment_099_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 648 27 27, g32p_row04_traceSegment_099_0648_0027, g32p_row04_traceSegment_099_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 702 13 14, g32p_row04_traceSegment_099_0702_0013, g32p_row04_traceSegment_099_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 729 13 14, g32p_row04_traceSegment_099_0729_0013, g32p_row04_traceSegment_099_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 702 27 27, g32p_row04_traceSegment_099_0702_0027, g32p_row04_traceSegment_099_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 648 54 54, g32p_row04_traceSegment_099_0648_0054, g32p_row04_traceSegment_099_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 756 13 14, g32p_row04_traceSegment_099_0756_0013, g32p_row04_traceSegment_099_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 783 13 14, g32p_row04_traceSegment_099_0783_0013, g32p_row04_traceSegment_099_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 756 27 27, g32p_row04_traceSegment_099_0756_0027, g32p_row04_traceSegment_099_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 810 13 14, g32p_row04_traceSegment_099_0810_0013, g32p_row04_traceSegment_099_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 837 13 14, g32p_row04_traceSegment_099_0837_0013, g32p_row04_traceSegment_099_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 810 27 27, g32p_row04_traceSegment_099_0810_0027, g32p_row04_traceSegment_099_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 756 54 54, g32p_row04_traceSegment_099_0756_0054, g32p_row04_traceSegment_099_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 648 108 108, g32p_row04_traceSegment_099_0648_0108, g32p_row04_traceSegment_099_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_099 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 432 216 216, g32p_row04_traceSegment_099_0432_0216, g32p_row04_traceSegment_099_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_099 0 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 0 432 432, g32p_row04_traceSegment_099_0000_0432, g32p_row04_traceSegment_099_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 864 13 14, g32p_row04_traceSegment_099_0864_0013, g32p_row04_traceSegment_099_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 891 13 14, g32p_row04_traceSegment_099_0891_0013, g32p_row04_traceSegment_099_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 864 27 27, g32p_row04_traceSegment_099_0864_0027, g32p_row04_traceSegment_099_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 918 13 14, g32p_row04_traceSegment_099_0918_0013, g32p_row04_traceSegment_099_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 945 13 14, g32p_row04_traceSegment_099_0945_0013, g32p_row04_traceSegment_099_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 918 27 27, g32p_row04_traceSegment_099_0918_0027, g32p_row04_traceSegment_099_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 864 54 54, g32p_row04_traceSegment_099_0864_0054, g32p_row04_traceSegment_099_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 972 13 14, g32p_row04_traceSegment_099_0972_0013, g32p_row04_traceSegment_099_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 999 13 14, g32p_row04_traceSegment_099_0999_0013, g32p_row04_traceSegment_099_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 972 27 27, g32p_row04_traceSegment_099_0972_0027, g32p_row04_traceSegment_099_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1026 13 14, g32p_row04_traceSegment_099_1026_0013, g32p_row04_traceSegment_099_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1053 13 14, g32p_row04_traceSegment_099_1053_0013, g32p_row04_traceSegment_099_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1026 27 27, g32p_row04_traceSegment_099_1026_0027, g32p_row04_traceSegment_099_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 972 54 54, g32p_row04_traceSegment_099_0972_0054, g32p_row04_traceSegment_099_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 864 108 108, g32p_row04_traceSegment_099_0864_0108, g32p_row04_traceSegment_099_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1080 13 14, g32p_row04_traceSegment_099_1080_0013, g32p_row04_traceSegment_099_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1107 13 14, g32p_row04_traceSegment_099_1107_0013, g32p_row04_traceSegment_099_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1080 27 27, g32p_row04_traceSegment_099_1080_0027, g32p_row04_traceSegment_099_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1134 13 14, g32p_row04_traceSegment_099_1134_0013, g32p_row04_traceSegment_099_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1161 13 14, g32p_row04_traceSegment_099_1161_0013, g32p_row04_traceSegment_099_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1134 27 27, g32p_row04_traceSegment_099_1134_0027, g32p_row04_traceSegment_099_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1080 54 54, g32p_row04_traceSegment_099_1080_0054, g32p_row04_traceSegment_099_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1201 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1188 13 14, g32p_row04_traceSegment_099_1188_0013, g32p_row04_traceSegment_099_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1215 13 14, g32p_row04_traceSegment_099_1215_0013, g32p_row04_traceSegment_099_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1188 27 27, g32p_row04_traceSegment_099_1188_0027, g32p_row04_traceSegment_099_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1242 13 14, g32p_row04_traceSegment_099_1242_0013, g32p_row04_traceSegment_099_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1282 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1269 13 14, g32p_row04_traceSegment_099_1269_0013, g32p_row04_traceSegment_099_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1242 27 27, g32p_row04_traceSegment_099_1242_0027, g32p_row04_traceSegment_099_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1188 54 54, g32p_row04_traceSegment_099_1188_0054, g32p_row04_traceSegment_099_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1080 108 108, g32p_row04_traceSegment_099_1080_0108, g32p_row04_traceSegment_099_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_099 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 864 216 216, g32p_row04_traceSegment_099_0864_0216, g32p_row04_traceSegment_099_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1296 13 14, g32p_row04_traceSegment_099_1296_0013, g32p_row04_traceSegment_099_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1323 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1336 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1323 13 14, g32p_row04_traceSegment_099_1323_0013, g32p_row04_traceSegment_099_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1296 27 27, g32p_row04_traceSegment_099_1296_0027, g32p_row04_traceSegment_099_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1350 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1350 13 14, g32p_row04_traceSegment_099_1350_0013, g32p_row04_traceSegment_099_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1377 13 14, g32p_row04_traceSegment_099_1377_0013, g32p_row04_traceSegment_099_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1350 27 27, g32p_row04_traceSegment_099_1350_0027, g32p_row04_traceSegment_099_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1296 54 54, g32p_row04_traceSegment_099_1296_0054, g32p_row04_traceSegment_099_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1404 13 14, g32p_row04_traceSegment_099_1404_0013, g32p_row04_traceSegment_099_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1431 13 14, g32p_row04_traceSegment_099_1431_0013, g32p_row04_traceSegment_099_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1404 27 27, g32p_row04_traceSegment_099_1404_0027, g32p_row04_traceSegment_099_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1458 13 14, g32p_row04_traceSegment_099_1458_0013, g32p_row04_traceSegment_099_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1485 13 14, g32p_row04_traceSegment_099_1485_0013, g32p_row04_traceSegment_099_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1458 27 27, g32p_row04_traceSegment_099_1458_0027, g32p_row04_traceSegment_099_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1404 54 54, g32p_row04_traceSegment_099_1404_0054, g32p_row04_traceSegment_099_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1296 108 108, g32p_row04_traceSegment_099_1296_0108, g32p_row04_traceSegment_099_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1512 13 14, g32p_row04_traceSegment_099_1512_0013, g32p_row04_traceSegment_099_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1539 13 14, g32p_row04_traceSegment_099_1539_0013, g32p_row04_traceSegment_099_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1512 27 27, g32p_row04_traceSegment_099_1512_0027, g32p_row04_traceSegment_099_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1566 13 14, g32p_row04_traceSegment_099_1566_0013, g32p_row04_traceSegment_099_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1593 13 14, g32p_row04_traceSegment_099_1593_0013, g32p_row04_traceSegment_099_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1566 27 27, g32p_row04_traceSegment_099_1566_0027, g32p_row04_traceSegment_099_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1512 54 54, g32p_row04_traceSegment_099_1512_0054, g32p_row04_traceSegment_099_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1620 13 14, g32p_row04_traceSegment_099_1620_0013, g32p_row04_traceSegment_099_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1647 13 14, g32p_row04_traceSegment_099_1647_0013, g32p_row04_traceSegment_099_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1620 27 27, g32p_row04_traceSegment_099_1620_0027, g32p_row04_traceSegment_099_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1674 13 14, g32p_row04_traceSegment_099_1674_0013, g32p_row04_traceSegment_099_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_099 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_099 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_099_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_099 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1701 13 14, g32p_row04_traceSegment_099_1701_0013, g32p_row04_traceSegment_099_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_099 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1674 27 27, g32p_row04_traceSegment_099_1674_0027, g32p_row04_traceSegment_099_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_099 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1620 54 54, g32p_row04_traceSegment_099_1620_0054, g32p_row04_traceSegment_099_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_099 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1512 108 108, g32p_row04_traceSegment_099_1512_0108, g32p_row04_traceSegment_099_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_099_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_099 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 1296 216 216, g32p_row04_traceSegment_099_1296_0216, g32p_row04_traceSegment_099_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_099 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 864 432 432, g32p_row04_traceSegment_099_0864_0432, g32p_row04_traceSegment_099_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_099_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_099 0 1728 = [1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_099 0 864 864, g32p_row04_traceSegment_099_0000_0864, g32p_row04_traceSegment_099_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_099 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 99 = [1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_099_0000_1728

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row04_traceSegment_100 (k : ℕ) : List ℤ :=
  if g32p_row04_supplierClassifier (Fin.ofNat 1728 k) = 100 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row04_characterValues (Fin.ofNat 1728 k))).val 1 else []

private theorem g32p_row04_traceSegment_100_0000_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 0 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0013_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 13 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0000_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 0 13 14, g32p_row04_traceSegment_100_0000_0013, g32p_row04_traceSegment_100_0013_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0027_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 27 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0040_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 40 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0027_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 27 13 14, g32p_row04_traceSegment_100_0027_0013, g32p_row04_traceSegment_100_0040_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0000_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 0 27 27, g32p_row04_traceSegment_100_0000_0027, g32p_row04_traceSegment_100_0027_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0054_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 54 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0067_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 67 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0054_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 54 13 14, g32p_row04_traceSegment_100_0054_0013, g32p_row04_traceSegment_100_0067_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0081_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 81 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0094_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 94 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0081_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 81 13 14, g32p_row04_traceSegment_100_0081_0013, g32p_row04_traceSegment_100_0094_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0054_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 54 27 27, g32p_row04_traceSegment_100_0054_0027, g32p_row04_traceSegment_100_0081_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0000_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 0 54 54, g32p_row04_traceSegment_100_0000_0054, g32p_row04_traceSegment_100_0054_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0108_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 108 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0121_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 121 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0108_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 108 13 14, g32p_row04_traceSegment_100_0108_0013, g32p_row04_traceSegment_100_0121_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0135_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 135 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0148_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 148 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0135_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 135 13 14, g32p_row04_traceSegment_100_0135_0013, g32p_row04_traceSegment_100_0148_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0108_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 108 27 27, g32p_row04_traceSegment_100_0108_0027, g32p_row04_traceSegment_100_0135_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0162_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 162 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0175_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 175 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0162_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 162 13 14, g32p_row04_traceSegment_100_0162_0013, g32p_row04_traceSegment_100_0175_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0189_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 189 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0202_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 202 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0189_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 189 13 14, g32p_row04_traceSegment_100_0189_0013, g32p_row04_traceSegment_100_0202_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0162_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 162 27 27, g32p_row04_traceSegment_100_0162_0027, g32p_row04_traceSegment_100_0189_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0108_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 108 54 54, g32p_row04_traceSegment_100_0108_0054, g32p_row04_traceSegment_100_0162_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0000_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 0 108 108, g32p_row04_traceSegment_100_0000_0108, g32p_row04_traceSegment_100_0108_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0216_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 216 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0229_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 229 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0216_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 216 13 14, g32p_row04_traceSegment_100_0216_0013, g32p_row04_traceSegment_100_0229_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0243_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 243 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0256_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 256 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0243_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 243 13 14, g32p_row04_traceSegment_100_0243_0013, g32p_row04_traceSegment_100_0256_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0216_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 216 27 27, g32p_row04_traceSegment_100_0216_0027, g32p_row04_traceSegment_100_0243_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0270_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 270 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0283_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 283 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0270_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 270 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 270 13 14, g32p_row04_traceSegment_100_0270_0013, g32p_row04_traceSegment_100_0283_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0297_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 297 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0310_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 310 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0297_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 297 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 297 13 14, g32p_row04_traceSegment_100_0297_0013, g32p_row04_traceSegment_100_0310_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0270_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 270 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 270 27 27, g32p_row04_traceSegment_100_0270_0027, g32p_row04_traceSegment_100_0297_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0216_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 216 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 216 54 54, g32p_row04_traceSegment_100_0216_0054, g32p_row04_traceSegment_100_0270_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0324_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 324 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0337_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 337 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0324_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 324 13 14, g32p_row04_traceSegment_100_0324_0013, g32p_row04_traceSegment_100_0337_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0351_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 351 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0364_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 364 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0351_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 351 13 14, g32p_row04_traceSegment_100_0351_0013, g32p_row04_traceSegment_100_0364_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0324_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 324 27 27, g32p_row04_traceSegment_100_0324_0027, g32p_row04_traceSegment_100_0351_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0378_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 378 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0391_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 391 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0378_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 378 13 14, g32p_row04_traceSegment_100_0378_0013, g32p_row04_traceSegment_100_0391_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0405_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 405 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0418_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 418 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0405_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 405 13 14, g32p_row04_traceSegment_100_0405_0013, g32p_row04_traceSegment_100_0418_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0378_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 378 27 27, g32p_row04_traceSegment_100_0378_0027, g32p_row04_traceSegment_100_0405_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0324_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 324 54 54, g32p_row04_traceSegment_100_0324_0054, g32p_row04_traceSegment_100_0378_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0216_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 216 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 216 108 108, g32p_row04_traceSegment_100_0216_0108, g32p_row04_traceSegment_100_0324_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0000_0432 : g32p_coeffSegment g32p_row04_traceSegment_100 0 432 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 0 216 216, g32p_row04_traceSegment_100_0000_0216, g32p_row04_traceSegment_100_0216_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0432_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 432 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0445_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 445 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0432_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 432 13 14, g32p_row04_traceSegment_100_0432_0013, g32p_row04_traceSegment_100_0445_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0459_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 459 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0472_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 472 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0459_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 459 13 14, g32p_row04_traceSegment_100_0459_0013, g32p_row04_traceSegment_100_0472_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0432_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 432 27 27, g32p_row04_traceSegment_100_0432_0027, g32p_row04_traceSegment_100_0459_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0486_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 486 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0499_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 499 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0486_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 486 13 14, g32p_row04_traceSegment_100_0486_0013, g32p_row04_traceSegment_100_0499_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0513_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 513 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0526_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 526 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0513_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 513 13 14, g32p_row04_traceSegment_100_0513_0013, g32p_row04_traceSegment_100_0526_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0486_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 486 27 27, g32p_row04_traceSegment_100_0486_0027, g32p_row04_traceSegment_100_0513_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0432_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 432 54 54, g32p_row04_traceSegment_100_0432_0054, g32p_row04_traceSegment_100_0486_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0540_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 540 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0553_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 553 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0540_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 540 13 14, g32p_row04_traceSegment_100_0540_0013, g32p_row04_traceSegment_100_0553_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0567_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 567 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0580_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 580 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0567_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 567 13 14, g32p_row04_traceSegment_100_0567_0013, g32p_row04_traceSegment_100_0580_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0540_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 540 27 27, g32p_row04_traceSegment_100_0540_0027, g32p_row04_traceSegment_100_0567_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0594_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 594 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0607_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 607 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0594_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 594 13 14, g32p_row04_traceSegment_100_0594_0013, g32p_row04_traceSegment_100_0607_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0621_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 621 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0634_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 634 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0621_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 621 13 14, g32p_row04_traceSegment_100_0621_0013, g32p_row04_traceSegment_100_0634_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0594_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 594 27 27, g32p_row04_traceSegment_100_0594_0027, g32p_row04_traceSegment_100_0621_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0540_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 540 54 54, g32p_row04_traceSegment_100_0540_0054, g32p_row04_traceSegment_100_0594_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0432_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 432 108 108, g32p_row04_traceSegment_100_0432_0108, g32p_row04_traceSegment_100_0540_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0648_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 648 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0661_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 661 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0648_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 648 13 14, g32p_row04_traceSegment_100_0648_0013, g32p_row04_traceSegment_100_0661_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0675_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 675 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0688_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 688 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0675_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 675 13 14, g32p_row04_traceSegment_100_0675_0013, g32p_row04_traceSegment_100_0688_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0648_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 648 27 27, g32p_row04_traceSegment_100_0648_0027, g32p_row04_traceSegment_100_0675_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0702_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 702 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0715_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 715 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0702_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 702 13 14, g32p_row04_traceSegment_100_0702_0013, g32p_row04_traceSegment_100_0715_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0729_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 729 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0742_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 742 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0729_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 729 13 14, g32p_row04_traceSegment_100_0729_0013, g32p_row04_traceSegment_100_0742_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0702_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 702 27 27, g32p_row04_traceSegment_100_0702_0027, g32p_row04_traceSegment_100_0729_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0648_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 648 54 54, g32p_row04_traceSegment_100_0648_0054, g32p_row04_traceSegment_100_0702_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0756_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 756 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0769_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 769 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0756_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 756 13 14, g32p_row04_traceSegment_100_0756_0013, g32p_row04_traceSegment_100_0769_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0783_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 783 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0796_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 796 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0783_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 783 13 14, g32p_row04_traceSegment_100_0783_0013, g32p_row04_traceSegment_100_0796_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0756_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 756 27 27, g32p_row04_traceSegment_100_0756_0027, g32p_row04_traceSegment_100_0783_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0810_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 810 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0823_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 823 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0810_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 810 13 14, g32p_row04_traceSegment_100_0810_0013, g32p_row04_traceSegment_100_0823_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0837_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 837 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0850_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 850 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0837_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 837 13 14, g32p_row04_traceSegment_100_0837_0013, g32p_row04_traceSegment_100_0850_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0810_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 810 27 27, g32p_row04_traceSegment_100_0810_0027, g32p_row04_traceSegment_100_0837_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0756_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 756 54 54, g32p_row04_traceSegment_100_0756_0054, g32p_row04_traceSegment_100_0810_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0648_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 648 108 108, g32p_row04_traceSegment_100_0648_0108, g32p_row04_traceSegment_100_0756_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0432_0432 : g32p_coeffSegment g32p_row04_traceSegment_100 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 432 216 216, g32p_row04_traceSegment_100_0432_0216, g32p_row04_traceSegment_100_0648_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0000_0864 : g32p_coeffSegment g32p_row04_traceSegment_100 0 864 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 0 432 432, g32p_row04_traceSegment_100_0000_0432, g32p_row04_traceSegment_100_0432_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0864_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 864 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0877_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 877 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0864_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 864 13 14, g32p_row04_traceSegment_100_0864_0013, g32p_row04_traceSegment_100_0877_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0891_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 891 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0904_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 904 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0891_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 891 13 14, g32p_row04_traceSegment_100_0891_0013, g32p_row04_traceSegment_100_0904_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0864_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 864 27 27, g32p_row04_traceSegment_100_0864_0027, g32p_row04_traceSegment_100_0891_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0918_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 918 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0931_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 931 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0918_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 918 13 14, g32p_row04_traceSegment_100_0918_0013, g32p_row04_traceSegment_100_0931_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0945_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 945 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0958_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 958 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0945_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 945 13 14, g32p_row04_traceSegment_100_0945_0013, g32p_row04_traceSegment_100_0958_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0918_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 918 27 27, g32p_row04_traceSegment_100_0918_0027, g32p_row04_traceSegment_100_0945_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0864_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 864 54 54, g32p_row04_traceSegment_100_0864_0054, g32p_row04_traceSegment_100_0918_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0972_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 972 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0985_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 985 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0972_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 972 13 14, g32p_row04_traceSegment_100_0972_0013, g32p_row04_traceSegment_100_0985_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0999_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 999 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1012_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1012 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_0999_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 999 13 14, g32p_row04_traceSegment_100_0999_0013, g32p_row04_traceSegment_100_1012_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0972_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 972 27 27, g32p_row04_traceSegment_100_0972_0027, g32p_row04_traceSegment_100_0999_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1026_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1026 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1039_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1039 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1026_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1026 13 14, g32p_row04_traceSegment_100_1026_0013, g32p_row04_traceSegment_100_1039_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1053_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1053 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1066_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1066 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1053_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1053 13 14, g32p_row04_traceSegment_100_1053_0013, g32p_row04_traceSegment_100_1066_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1026_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1026 27 27, g32p_row04_traceSegment_100_1026_0027, g32p_row04_traceSegment_100_1053_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0972_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 972 54 54, g32p_row04_traceSegment_100_0972_0054, g32p_row04_traceSegment_100_1026_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0864_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 864 108 108, g32p_row04_traceSegment_100_0864_0108, g32p_row04_traceSegment_100_0972_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1080_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1080 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1093_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1093 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1080_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1080 13 14, g32p_row04_traceSegment_100_1080_0013, g32p_row04_traceSegment_100_1093_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1107_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1107 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1120_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1120 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1107_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1107 13 14, g32p_row04_traceSegment_100_1107_0013, g32p_row04_traceSegment_100_1120_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1080_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1080 27 27, g32p_row04_traceSegment_100_1080_0027, g32p_row04_traceSegment_100_1107_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1134_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1134 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1147_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1147 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1134_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1134 13 14, g32p_row04_traceSegment_100_1134_0013, g32p_row04_traceSegment_100_1147_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1161_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1161 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1174_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1174 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1161_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1161 13 14, g32p_row04_traceSegment_100_1161_0013, g32p_row04_traceSegment_100_1174_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1134_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1134 27 27, g32p_row04_traceSegment_100_1134_0027, g32p_row04_traceSegment_100_1161_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1080_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1080 54 54, g32p_row04_traceSegment_100_1080_0054, g32p_row04_traceSegment_100_1134_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1188_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1188 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1201_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1201 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1188_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1188 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1188 13 14, g32p_row04_traceSegment_100_1188_0013, g32p_row04_traceSegment_100_1201_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1215_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1215 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1228_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1228 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1215_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1215 13 14, g32p_row04_traceSegment_100_1215_0013, g32p_row04_traceSegment_100_1228_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1188_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1188 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1188 27 27, g32p_row04_traceSegment_100_1188_0027, g32p_row04_traceSegment_100_1215_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1242_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1242 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1255_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1255 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1242_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1242 13 14, g32p_row04_traceSegment_100_1242_0013, g32p_row04_traceSegment_100_1255_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1269_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1269 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1282_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1282 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1269_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1269 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1269 13 14, g32p_row04_traceSegment_100_1269_0013, g32p_row04_traceSegment_100_1282_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1242_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1242 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1242 27 27, g32p_row04_traceSegment_100_1242_0027, g32p_row04_traceSegment_100_1269_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1188_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 1188 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1188 54 54, g32p_row04_traceSegment_100_1188_0054, g32p_row04_traceSegment_100_1242_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1080_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 1080 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1080 108 108, g32p_row04_traceSegment_100_1080_0108, g32p_row04_traceSegment_100_1188_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0864_0432 : g32p_coeffSegment g32p_row04_traceSegment_100 864 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 864 216 216, g32p_row04_traceSegment_100_0864_0216, g32p_row04_traceSegment_100_1080_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1296_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1296 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1309_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1309 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1296_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1296 13 14, g32p_row04_traceSegment_100_1296_0013, g32p_row04_traceSegment_100_1309_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1323_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1323 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1336_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1336 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1323_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1323 27 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1323 13 14, g32p_row04_traceSegment_100_1323_0013, g32p_row04_traceSegment_100_1336_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1296_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1296 54 = [0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1296 27 27, g32p_row04_traceSegment_100_1296_0027, g32p_row04_traceSegment_100_1323_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1350_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1350 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1363_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1363 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1350_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1350 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1350 13 14, g32p_row04_traceSegment_100_1350_0013, g32p_row04_traceSegment_100_1363_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1377_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1377 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1390_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1390 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1377_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1377 13 14, g32p_row04_traceSegment_100_1377_0013, g32p_row04_traceSegment_100_1390_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1350_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1350 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1350 27 27, g32p_row04_traceSegment_100_1350_0027, g32p_row04_traceSegment_100_1377_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1296_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 1296 108 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1296 54 54, g32p_row04_traceSegment_100_1296_0054, g32p_row04_traceSegment_100_1350_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1404_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1404 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1417_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1417 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1404_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1404 13 14, g32p_row04_traceSegment_100_1404_0013, g32p_row04_traceSegment_100_1417_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1431_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1431 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1444_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1444 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1431_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1431 13 14, g32p_row04_traceSegment_100_1431_0013, g32p_row04_traceSegment_100_1444_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1404_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1404 27 27, g32p_row04_traceSegment_100_1404_0027, g32p_row04_traceSegment_100_1431_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1458_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1458 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1471_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1471 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1458_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1458 13 14, g32p_row04_traceSegment_100_1458_0013, g32p_row04_traceSegment_100_1471_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1485_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1485 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1498_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1498 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1485_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1485 13 14, g32p_row04_traceSegment_100_1485_0013, g32p_row04_traceSegment_100_1498_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1458_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1458 27 27, g32p_row04_traceSegment_100_1458_0027, g32p_row04_traceSegment_100_1485_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1404_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1404 54 54, g32p_row04_traceSegment_100_1404_0054, g32p_row04_traceSegment_100_1458_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1296_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 1296 216 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1296 108 108, g32p_row04_traceSegment_100_1296_0108, g32p_row04_traceSegment_100_1404_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1512_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1512 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1525_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1525 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1512_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1512 13 14, g32p_row04_traceSegment_100_1512_0013, g32p_row04_traceSegment_100_1525_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1539_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1539 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1552_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1552 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1539_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1539 13 14, g32p_row04_traceSegment_100_1539_0013, g32p_row04_traceSegment_100_1552_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1512_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1512 27 27, g32p_row04_traceSegment_100_1512_0027, g32p_row04_traceSegment_100_1539_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1566_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1566 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1579_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1579 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1566_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1566 13 14, g32p_row04_traceSegment_100_1566_0013, g32p_row04_traceSegment_100_1579_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1593_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1593 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1606_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1606 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1593_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1593 13 14, g32p_row04_traceSegment_100_1593_0013, g32p_row04_traceSegment_100_1606_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1566_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1566 27 27, g32p_row04_traceSegment_100_1566_0027, g32p_row04_traceSegment_100_1593_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1512_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1512 54 54, g32p_row04_traceSegment_100_1512_0054, g32p_row04_traceSegment_100_1566_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1620_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1620 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1633_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1633 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1620_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1620 13 14, g32p_row04_traceSegment_100_1620_0013, g32p_row04_traceSegment_100_1633_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1647_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1647 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1660_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1660 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1647_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1647 13 14, g32p_row04_traceSegment_100_1647_0013, g32p_row04_traceSegment_100_1660_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1620_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1620 27 27, g32p_row04_traceSegment_100_1620_0027, g32p_row04_traceSegment_100_1647_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1674_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1674 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1687_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1687 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1674_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1674 13 14, g32p_row04_traceSegment_100_1674_0013, g32p_row04_traceSegment_100_1687_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1701_0013 : g32p_coeffSegment g32p_row04_traceSegment_100 1701 13 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1714_0014 : g32p_coeffSegment g32p_row04_traceSegment_100 1714 14 = [] := by
  decide +kernel

private theorem g32p_row04_traceSegment_100_1701_0027 : g32p_coeffSegment g32p_row04_traceSegment_100 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1701 13 14, g32p_row04_traceSegment_100_1701_0013, g32p_row04_traceSegment_100_1714_0014]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1674_0054 : g32p_coeffSegment g32p_row04_traceSegment_100 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1674 27 27, g32p_row04_traceSegment_100_1674_0027, g32p_row04_traceSegment_100_1701_0027]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1620_0108 : g32p_coeffSegment g32p_row04_traceSegment_100 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1620 54 54, g32p_row04_traceSegment_100_1620_0054, g32p_row04_traceSegment_100_1674_0054]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1512_0216 : g32p_coeffSegment g32p_row04_traceSegment_100 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1512 108 108, g32p_row04_traceSegment_100_1512_0108, g32p_row04_traceSegment_100_1620_0108]
  decide +kernel

private theorem g32p_row04_traceSegment_100_1296_0432 : g32p_coeffSegment g32p_row04_traceSegment_100 1296 432 = [0, 2, 1] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 1296 216 216, g32p_row04_traceSegment_100_1296_0216, g32p_row04_traceSegment_100_1512_0216]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0864_0864 : g32p_coeffSegment g32p_row04_traceSegment_100 864 864 = [0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 864 432 432, g32p_row04_traceSegment_100_0864_0432, g32p_row04_traceSegment_100_1296_0432]
  decide +kernel

private theorem g32p_row04_traceSegment_100_0000_1728 : g32p_coeffSegment g32p_row04_traceSegment_100 0 1728 = [0, 4, 4] := by
  rw [g32p_coeffSegment_add g32p_row04_traceSegment_100 0 864 864, g32p_row04_traceSegment_100_0000_0864, g32p_row04_traceSegment_100_0864_0864]
  decide +kernel

theorem g32p_row04_traceCoefficients_100 :
    g32p_supplierTraceCoefficients g32p_row04_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row04_characterValues j)).val) 100 = [0, 4, 4] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row04_traceSegment_100_0000_1728

end HodgeLean.Foundations.Program

end
end
