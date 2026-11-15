import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0298

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_035 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 35 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_035_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 0 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 0 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 13 14, g32p_row02_traceSegment_035_0000_0013, g32p_row02_traceSegment_035_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 27 13 14, g32p_row02_traceSegment_035_0027_0013, g32p_row02_traceSegment_035_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 0 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 27 27, g32p_row02_traceSegment_035_0000_0027, g32p_row02_traceSegment_035_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 67 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 54 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 54 13 14, g32p_row02_traceSegment_035_0054_0013, g32p_row02_traceSegment_035_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 81 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 81 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 81 13 14, g32p_row02_traceSegment_035_0081_0013, g32p_row02_traceSegment_035_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 54 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 54 27 27, g32p_row02_traceSegment_035_0054_0027, g32p_row02_traceSegment_035_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 0 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 54 54, g32p_row02_traceSegment_035_0000_0054, g32p_row02_traceSegment_035_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 108 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 108 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 108 13 14, g32p_row02_traceSegment_035_0108_0013, g32p_row02_traceSegment_035_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 135 13 14, g32p_row02_traceSegment_035_0135_0013, g32p_row02_traceSegment_035_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 108 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 108 27 27, g32p_row02_traceSegment_035_0108_0027, g32p_row02_traceSegment_035_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 175 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 162 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 162 13 14, g32p_row02_traceSegment_035_0162_0013, g32p_row02_traceSegment_035_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 189 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 189 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 189 13 14, g32p_row02_traceSegment_035_0189_0013, g32p_row02_traceSegment_035_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 162 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 162 27 27, g32p_row02_traceSegment_035_0162_0027, g32p_row02_traceSegment_035_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 108 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 108 54 54, g32p_row02_traceSegment_035_0108_0054, g32p_row02_traceSegment_035_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 0 216 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 108 108, g32p_row02_traceSegment_035_0000_0108, g32p_row02_traceSegment_035_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 216 13 14, g32p_row02_traceSegment_035_0216_0013, g32p_row02_traceSegment_035_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 243 13 14, g32p_row02_traceSegment_035_0243_0013, g32p_row02_traceSegment_035_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 216 27 27, g32p_row02_traceSegment_035_0216_0027, g32p_row02_traceSegment_035_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 270 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 270 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 270 13 14, g32p_row02_traceSegment_035_0270_0013, g32p_row02_traceSegment_035_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 297 13 14, g32p_row02_traceSegment_035_0297_0013, g32p_row02_traceSegment_035_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 270 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 270 27 27, g32p_row02_traceSegment_035_0270_0027, g32p_row02_traceSegment_035_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 216 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 216 54 54, g32p_row02_traceSegment_035_0216_0054, g32p_row02_traceSegment_035_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 324 13 14, g32p_row02_traceSegment_035_0324_0013, g32p_row02_traceSegment_035_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 351 13 14, g32p_row02_traceSegment_035_0351_0013, g32p_row02_traceSegment_035_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 324 27 27, g32p_row02_traceSegment_035_0324_0027, g32p_row02_traceSegment_035_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 378 13 14, g32p_row02_traceSegment_035_0378_0013, g32p_row02_traceSegment_035_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 405 13 14, g32p_row02_traceSegment_035_0405_0013, g32p_row02_traceSegment_035_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 378 27 27, g32p_row02_traceSegment_035_0378_0027, g32p_row02_traceSegment_035_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 324 54 54, g32p_row02_traceSegment_035_0324_0054, g32p_row02_traceSegment_035_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 216 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 216 108 108, g32p_row02_traceSegment_035_0216_0108, g32p_row02_traceSegment_035_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 0 432 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 216 216, g32p_row02_traceSegment_035_0000_0216, g32p_row02_traceSegment_035_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 432 13 14, g32p_row02_traceSegment_035_0432_0013, g32p_row02_traceSegment_035_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 459 13 14, g32p_row02_traceSegment_035_0459_0013, g32p_row02_traceSegment_035_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 432 27 27, g32p_row02_traceSegment_035_0432_0027, g32p_row02_traceSegment_035_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 486 13 14, g32p_row02_traceSegment_035_0486_0013, g32p_row02_traceSegment_035_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 513 13 14, g32p_row02_traceSegment_035_0513_0013, g32p_row02_traceSegment_035_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 486 27 27, g32p_row02_traceSegment_035_0486_0027, g32p_row02_traceSegment_035_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 432 54 54, g32p_row02_traceSegment_035_0432_0054, g32p_row02_traceSegment_035_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 540 13 14, g32p_row02_traceSegment_035_0540_0013, g32p_row02_traceSegment_035_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 567 13 14, g32p_row02_traceSegment_035_0567_0013, g32p_row02_traceSegment_035_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 540 27 27, g32p_row02_traceSegment_035_0540_0027, g32p_row02_traceSegment_035_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 594 13 14, g32p_row02_traceSegment_035_0594_0013, g32p_row02_traceSegment_035_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 621 13 14, g32p_row02_traceSegment_035_0621_0013, g32p_row02_traceSegment_035_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 594 27 27, g32p_row02_traceSegment_035_0594_0027, g32p_row02_traceSegment_035_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 540 54 54, g32p_row02_traceSegment_035_0540_0054, g32p_row02_traceSegment_035_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 432 108 108, g32p_row02_traceSegment_035_0432_0108, g32p_row02_traceSegment_035_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 648 13 14, g32p_row02_traceSegment_035_0648_0013, g32p_row02_traceSegment_035_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 675 13 14, g32p_row02_traceSegment_035_0675_0013, g32p_row02_traceSegment_035_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 648 27 27, g32p_row02_traceSegment_035_0648_0027, g32p_row02_traceSegment_035_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 702 13 14, g32p_row02_traceSegment_035_0702_0013, g32p_row02_traceSegment_035_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 729 13 14, g32p_row02_traceSegment_035_0729_0013, g32p_row02_traceSegment_035_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 702 27 27, g32p_row02_traceSegment_035_0702_0027, g32p_row02_traceSegment_035_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 648 54 54, g32p_row02_traceSegment_035_0648_0054, g32p_row02_traceSegment_035_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 756 13 14, g32p_row02_traceSegment_035_0756_0013, g32p_row02_traceSegment_035_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 783 13 14, g32p_row02_traceSegment_035_0783_0013, g32p_row02_traceSegment_035_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 756 27 27, g32p_row02_traceSegment_035_0756_0027, g32p_row02_traceSegment_035_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 810 13 14, g32p_row02_traceSegment_035_0810_0013, g32p_row02_traceSegment_035_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 837 13 14, g32p_row02_traceSegment_035_0837_0013, g32p_row02_traceSegment_035_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 810 27 27, g32p_row02_traceSegment_035_0810_0027, g32p_row02_traceSegment_035_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 756 54 54, g32p_row02_traceSegment_035_0756_0054, g32p_row02_traceSegment_035_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 648 108 108, g32p_row02_traceSegment_035_0648_0108, g32p_row02_traceSegment_035_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 432 216 216, g32p_row02_traceSegment_035_0432_0216, g32p_row02_traceSegment_035_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_035 0 864 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 432 432, g32p_row02_traceSegment_035_0000_0432, g32p_row02_traceSegment_035_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 864 13 14, g32p_row02_traceSegment_035_0864_0013, g32p_row02_traceSegment_035_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 891 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 904 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 891 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 891 13 14, g32p_row02_traceSegment_035_0891_0013, g32p_row02_traceSegment_035_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 864 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 864 27 27, g32p_row02_traceSegment_035_0864_0027, g32p_row02_traceSegment_035_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 918 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 918 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 918 13 14, g32p_row02_traceSegment_035_0918_0013, g32p_row02_traceSegment_035_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 945 13 14, g32p_row02_traceSegment_035_0945_0013, g32p_row02_traceSegment_035_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 918 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 918 27 27, g32p_row02_traceSegment_035_0918_0027, g32p_row02_traceSegment_035_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 864 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 864 54 54, g32p_row02_traceSegment_035_0864_0054, g32p_row02_traceSegment_035_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 972 13 14, g32p_row02_traceSegment_035_0972_0013, g32p_row02_traceSegment_035_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 999 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 999 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 999 13 14, g32p_row02_traceSegment_035_0999_0013, g32p_row02_traceSegment_035_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 972 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 972 27 27, g32p_row02_traceSegment_035_0972_0027, g32p_row02_traceSegment_035_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1026 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1039 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1026 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1026 13 14, g32p_row02_traceSegment_035_1026_0013, g32p_row02_traceSegment_035_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1066 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1053 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1053 13 14, g32p_row02_traceSegment_035_1053_0013, g32p_row02_traceSegment_035_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1026 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1026 27 27, g32p_row02_traceSegment_035_1026_0027, g32p_row02_traceSegment_035_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 972 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 972 54 54, g32p_row02_traceSegment_035_0972_0054, g32p_row02_traceSegment_035_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 864 216 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 864 108 108, g32p_row02_traceSegment_035_0864_0108, g32p_row02_traceSegment_035_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1080 13 14, g32p_row02_traceSegment_035_1080_0013, g32p_row02_traceSegment_035_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1107 13 14, g32p_row02_traceSegment_035_1107_0013, g32p_row02_traceSegment_035_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1080 27 27, g32p_row02_traceSegment_035_1080_0027, g32p_row02_traceSegment_035_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1134 13 14, g32p_row02_traceSegment_035_1134_0013, g32p_row02_traceSegment_035_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1161 13 14, g32p_row02_traceSegment_035_1161_0013, g32p_row02_traceSegment_035_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1134 27 27, g32p_row02_traceSegment_035_1134_0027, g32p_row02_traceSegment_035_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1080 54 54, g32p_row02_traceSegment_035_1080_0054, g32p_row02_traceSegment_035_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1188 13 14, g32p_row02_traceSegment_035_1188_0013, g32p_row02_traceSegment_035_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1215 13 14, g32p_row02_traceSegment_035_1215_0013, g32p_row02_traceSegment_035_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1188 27 27, g32p_row02_traceSegment_035_1188_0027, g32p_row02_traceSegment_035_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1242 13 14, g32p_row02_traceSegment_035_1242_0013, g32p_row02_traceSegment_035_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1269 13 14, g32p_row02_traceSegment_035_1269_0013, g32p_row02_traceSegment_035_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1242 27 27, g32p_row02_traceSegment_035_1242_0027, g32p_row02_traceSegment_035_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1188 54 54, g32p_row02_traceSegment_035_1188_0054, g32p_row02_traceSegment_035_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1080 108 108, g32p_row02_traceSegment_035_1080_0108, g32p_row02_traceSegment_035_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 864 432 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 864 216 216, g32p_row02_traceSegment_035_0864_0216, g32p_row02_traceSegment_035_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1309 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1296 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1296 13 14, g32p_row02_traceSegment_035_1296_0013, g32p_row02_traceSegment_035_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1323 13 14, g32p_row02_traceSegment_035_1323_0013, g32p_row02_traceSegment_035_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1296 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1296 27 27, g32p_row02_traceSegment_035_1296_0027, g32p_row02_traceSegment_035_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1363 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1350 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1350 13 14, g32p_row02_traceSegment_035_1350_0013, g32p_row02_traceSegment_035_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1377 13 14, g32p_row02_traceSegment_035_1377_0013, g32p_row02_traceSegment_035_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1350 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1350 27 27, g32p_row02_traceSegment_035_1350_0027, g32p_row02_traceSegment_035_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1296 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1296 54 54, g32p_row02_traceSegment_035_1296_0054, g32p_row02_traceSegment_035_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1404 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1404 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1404 13 14, g32p_row02_traceSegment_035_1404_0013, g32p_row02_traceSegment_035_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1431 13 14, g32p_row02_traceSegment_035_1431_0013, g32p_row02_traceSegment_035_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1404 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1404 27 27, g32p_row02_traceSegment_035_1404_0027, g32p_row02_traceSegment_035_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1458 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1458 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1458 13 14, g32p_row02_traceSegment_035_1458_0013, g32p_row02_traceSegment_035_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1485 13 14, g32p_row02_traceSegment_035_1485_0013, g32p_row02_traceSegment_035_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1458 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1458 27 27, g32p_row02_traceSegment_035_1458_0027, g32p_row02_traceSegment_035_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1404 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1404 54 54, g32p_row02_traceSegment_035_1404_0054, g32p_row02_traceSegment_035_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 1296 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1296 108 108, g32p_row02_traceSegment_035_1296_0108, g32p_row02_traceSegment_035_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1512 13 14, g32p_row02_traceSegment_035_1512_0013, g32p_row02_traceSegment_035_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1539 13 14, g32p_row02_traceSegment_035_1539_0013, g32p_row02_traceSegment_035_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1512 27 27, g32p_row02_traceSegment_035_1512_0027, g32p_row02_traceSegment_035_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1566 13 14, g32p_row02_traceSegment_035_1566_0013, g32p_row02_traceSegment_035_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1606 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1593 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1593 13 14, g32p_row02_traceSegment_035_1593_0013, g32p_row02_traceSegment_035_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1566 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1566 27 27, g32p_row02_traceSegment_035_1566_0027, g32p_row02_traceSegment_035_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1512 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1512 54 54, g32p_row02_traceSegment_035_1512_0054, g32p_row02_traceSegment_035_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1620 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1620 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1620 13 14, g32p_row02_traceSegment_035_1620_0013, g32p_row02_traceSegment_035_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1647 13 14, g32p_row02_traceSegment_035_1647_0013, g32p_row02_traceSegment_035_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1620 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1620 27 27, g32p_row02_traceSegment_035_1620_0027, g32p_row02_traceSegment_035_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1674 13 14, g32p_row02_traceSegment_035_1674_0013, g32p_row02_traceSegment_035_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1701 13 14, g32p_row02_traceSegment_035_1701_0013, g32p_row02_traceSegment_035_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1674 27 27, g32p_row02_traceSegment_035_1674_0027, g32p_row02_traceSegment_035_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1620 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1620 54 54, g32p_row02_traceSegment_035_1620_0054, g32p_row02_traceSegment_035_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 1512 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1512 108 108, g32p_row02_traceSegment_035_1512_0108, g32p_row02_traceSegment_035_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 1296 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1296 216 216, g32p_row02_traceSegment_035_1296_0216, g32p_row02_traceSegment_035_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_035 864 864 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 864 432 432, g32p_row02_traceSegment_035_0864_0432, g32p_row02_traceSegment_035_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_035 0 1728 = [0, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 864 864, g32p_row02_traceSegment_035_0000_0864, g32p_row02_traceSegment_035_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1728 13 14, g32p_row02_traceSegment_035_1728_0013, g32p_row02_traceSegment_035_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1755 13 14, g32p_row02_traceSegment_035_1755_0013, g32p_row02_traceSegment_035_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1728 27 27, g32p_row02_traceSegment_035_1728_0027, g32p_row02_traceSegment_035_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1782 13 14, g32p_row02_traceSegment_035_1782_0013, g32p_row02_traceSegment_035_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1809 13 14, g32p_row02_traceSegment_035_1809_0013, g32p_row02_traceSegment_035_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1782 27 27, g32p_row02_traceSegment_035_1782_0027, g32p_row02_traceSegment_035_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1728 54 54, g32p_row02_traceSegment_035_1728_0054, g32p_row02_traceSegment_035_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1836 13 14, g32p_row02_traceSegment_035_1836_0013, g32p_row02_traceSegment_035_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1863 13 14, g32p_row02_traceSegment_035_1863_0013, g32p_row02_traceSegment_035_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1836 27 27, g32p_row02_traceSegment_035_1836_0027, g32p_row02_traceSegment_035_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1890 13 14, g32p_row02_traceSegment_035_1890_0013, g32p_row02_traceSegment_035_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1917 13 14, g32p_row02_traceSegment_035_1917_0013, g32p_row02_traceSegment_035_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1890 27 27, g32p_row02_traceSegment_035_1890_0027, g32p_row02_traceSegment_035_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1836 54 54, g32p_row02_traceSegment_035_1836_0054, g32p_row02_traceSegment_035_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1728 108 108, g32p_row02_traceSegment_035_1728_0108, g32p_row02_traceSegment_035_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1957 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1944 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1944 13 14, g32p_row02_traceSegment_035_1944_0013, g32p_row02_traceSegment_035_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1971 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1971 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1971 13 14, g32p_row02_traceSegment_035_1971_0013, g32p_row02_traceSegment_035_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1944 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1944 27 27, g32p_row02_traceSegment_035_1944_0027, g32p_row02_traceSegment_035_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1998 13 14, g32p_row02_traceSegment_035_1998_0013, g32p_row02_traceSegment_035_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2025 13 14, g32p_row02_traceSegment_035_2025_0013, g32p_row02_traceSegment_035_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1998 27 27, g32p_row02_traceSegment_035_1998_0027, g32p_row02_traceSegment_035_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 1944 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1944 54 54, g32p_row02_traceSegment_035_1944_0054, g32p_row02_traceSegment_035_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2052 13 14, g32p_row02_traceSegment_035_2052_0013, g32p_row02_traceSegment_035_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2079 13 14, g32p_row02_traceSegment_035_2079_0013, g32p_row02_traceSegment_035_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2052 27 27, g32p_row02_traceSegment_035_2052_0027, g32p_row02_traceSegment_035_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2106 13 14, g32p_row02_traceSegment_035_2106_0013, g32p_row02_traceSegment_035_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2133 13 14, g32p_row02_traceSegment_035_2133_0013, g32p_row02_traceSegment_035_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2106 27 27, g32p_row02_traceSegment_035_2106_0027, g32p_row02_traceSegment_035_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2052 54 54, g32p_row02_traceSegment_035_2052_0054, g32p_row02_traceSegment_035_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 1944 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1944 108 108, g32p_row02_traceSegment_035_1944_0108, g32p_row02_traceSegment_035_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1728 216 216, g32p_row02_traceSegment_035_1728_0216, g32p_row02_traceSegment_035_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2160 13 14, g32p_row02_traceSegment_035_2160_0013, g32p_row02_traceSegment_035_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2187 13 14, g32p_row02_traceSegment_035_2187_0013, g32p_row02_traceSegment_035_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2160 27 27, g32p_row02_traceSegment_035_2160_0027, g32p_row02_traceSegment_035_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2214 13 14, g32p_row02_traceSegment_035_2214_0013, g32p_row02_traceSegment_035_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2241 13 14, g32p_row02_traceSegment_035_2241_0013, g32p_row02_traceSegment_035_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2214 27 27, g32p_row02_traceSegment_035_2214_0027, g32p_row02_traceSegment_035_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2160 54 54, g32p_row02_traceSegment_035_2160_0054, g32p_row02_traceSegment_035_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2268 13 14, g32p_row02_traceSegment_035_2268_0013, g32p_row02_traceSegment_035_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2295 13 14, g32p_row02_traceSegment_035_2295_0013, g32p_row02_traceSegment_035_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2268 27 27, g32p_row02_traceSegment_035_2268_0027, g32p_row02_traceSegment_035_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2322 13 14, g32p_row02_traceSegment_035_2322_0013, g32p_row02_traceSegment_035_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2349 13 14, g32p_row02_traceSegment_035_2349_0013, g32p_row02_traceSegment_035_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2322 27 27, g32p_row02_traceSegment_035_2322_0027, g32p_row02_traceSegment_035_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2268 54 54, g32p_row02_traceSegment_035_2268_0054, g32p_row02_traceSegment_035_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2160 108 108, g32p_row02_traceSegment_035_2160_0108, g32p_row02_traceSegment_035_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2376 13 14, g32p_row02_traceSegment_035_2376_0013, g32p_row02_traceSegment_035_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2403 13 14, g32p_row02_traceSegment_035_2403_0013, g32p_row02_traceSegment_035_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2376 27 27, g32p_row02_traceSegment_035_2376_0027, g32p_row02_traceSegment_035_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2430 13 14, g32p_row02_traceSegment_035_2430_0013, g32p_row02_traceSegment_035_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2470 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2457 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2457 13 14, g32p_row02_traceSegment_035_2457_0013, g32p_row02_traceSegment_035_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2430 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2430 27 27, g32p_row02_traceSegment_035_2430_0027, g32p_row02_traceSegment_035_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2376 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2376 54 54, g32p_row02_traceSegment_035_2376_0054, g32p_row02_traceSegment_035_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2484 13 14, g32p_row02_traceSegment_035_2484_0013, g32p_row02_traceSegment_035_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2511 13 14, g32p_row02_traceSegment_035_2511_0013, g32p_row02_traceSegment_035_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2484 27 27, g32p_row02_traceSegment_035_2484_0027, g32p_row02_traceSegment_035_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2538 13 14, g32p_row02_traceSegment_035_2538_0013, g32p_row02_traceSegment_035_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2565 13 14, g32p_row02_traceSegment_035_2565_0013, g32p_row02_traceSegment_035_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2538 27 27, g32p_row02_traceSegment_035_2538_0027, g32p_row02_traceSegment_035_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2484 54 54, g32p_row02_traceSegment_035_2484_0054, g32p_row02_traceSegment_035_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 2376 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2376 108 108, g32p_row02_traceSegment_035_2376_0108, g32p_row02_traceSegment_035_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 2160 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2160 216 216, g32p_row02_traceSegment_035_2160_0216, g32p_row02_traceSegment_035_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1728 432 432, g32p_row02_traceSegment_035_1728_0432, g32p_row02_traceSegment_035_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2592 13 14, g32p_row02_traceSegment_035_2592_0013, g32p_row02_traceSegment_035_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2619 13 14, g32p_row02_traceSegment_035_2619_0013, g32p_row02_traceSegment_035_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2592 27 27, g32p_row02_traceSegment_035_2592_0027, g32p_row02_traceSegment_035_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2659 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2646 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2646 13 14, g32p_row02_traceSegment_035_2646_0013, g32p_row02_traceSegment_035_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2673 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2686 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2673 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2673 13 14, g32p_row02_traceSegment_035_2673_0013, g32p_row02_traceSegment_035_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2646 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2646 27 27, g32p_row02_traceSegment_035_2646_0027, g32p_row02_traceSegment_035_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2592 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2592 54 54, g32p_row02_traceSegment_035_2592_0054, g32p_row02_traceSegment_035_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2700 13 14, g32p_row02_traceSegment_035_2700_0013, g32p_row02_traceSegment_035_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2727 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2740 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2727 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2727 13 14, g32p_row02_traceSegment_035_2727_0013, g32p_row02_traceSegment_035_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2700 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2700 27 27, g32p_row02_traceSegment_035_2700_0027, g32p_row02_traceSegment_035_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2754 13 14, g32p_row02_traceSegment_035_2754_0013, g32p_row02_traceSegment_035_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2781 13 14, g32p_row02_traceSegment_035_2781_0013, g32p_row02_traceSegment_035_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2754 27 27, g32p_row02_traceSegment_035_2754_0027, g32p_row02_traceSegment_035_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2700 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2700 54 54, g32p_row02_traceSegment_035_2700_0054, g32p_row02_traceSegment_035_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 2592 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2592 108 108, g32p_row02_traceSegment_035_2592_0108, g32p_row02_traceSegment_035_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2808 13 14, g32p_row02_traceSegment_035_2808_0013, g32p_row02_traceSegment_035_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2835 13 14, g32p_row02_traceSegment_035_2835_0013, g32p_row02_traceSegment_035_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2808 27 27, g32p_row02_traceSegment_035_2808_0027, g32p_row02_traceSegment_035_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2862 13 14, g32p_row02_traceSegment_035_2862_0013, g32p_row02_traceSegment_035_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2889 13 14, g32p_row02_traceSegment_035_2889_0013, g32p_row02_traceSegment_035_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2862 27 27, g32p_row02_traceSegment_035_2862_0027, g32p_row02_traceSegment_035_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2808 54 54, g32p_row02_traceSegment_035_2808_0054, g32p_row02_traceSegment_035_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2916 13 14, g32p_row02_traceSegment_035_2916_0013, g32p_row02_traceSegment_035_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2943 13 14, g32p_row02_traceSegment_035_2943_0013, g32p_row02_traceSegment_035_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2916 27 27, g32p_row02_traceSegment_035_2916_0027, g32p_row02_traceSegment_035_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2970 13 14, g32p_row02_traceSegment_035_2970_0013, g32p_row02_traceSegment_035_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2997 13 14, g32p_row02_traceSegment_035_2997_0013, g32p_row02_traceSegment_035_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2970 27 27, g32p_row02_traceSegment_035_2970_0027, g32p_row02_traceSegment_035_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2916 54 54, g32p_row02_traceSegment_035_2916_0054, g32p_row02_traceSegment_035_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2808 108 108, g32p_row02_traceSegment_035_2808_0108, g32p_row02_traceSegment_035_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 2592 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2592 216 216, g32p_row02_traceSegment_035_2592_0216, g32p_row02_traceSegment_035_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3024 13 14, g32p_row02_traceSegment_035_3024_0013, g32p_row02_traceSegment_035_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3051 13 14, g32p_row02_traceSegment_035_3051_0013, g32p_row02_traceSegment_035_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3024 27 27, g32p_row02_traceSegment_035_3024_0027, g32p_row02_traceSegment_035_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3078 13 14, g32p_row02_traceSegment_035_3078_0013, g32p_row02_traceSegment_035_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3105 13 14, g32p_row02_traceSegment_035_3105_0013, g32p_row02_traceSegment_035_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3078 27 27, g32p_row02_traceSegment_035_3078_0027, g32p_row02_traceSegment_035_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3024 54 54, g32p_row02_traceSegment_035_3024_0054, g32p_row02_traceSegment_035_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3132 13 14, g32p_row02_traceSegment_035_3132_0013, g32p_row02_traceSegment_035_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3159 13 14, g32p_row02_traceSegment_035_3159_0013, g32p_row02_traceSegment_035_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3132 27 27, g32p_row02_traceSegment_035_3132_0027, g32p_row02_traceSegment_035_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3186 13 14, g32p_row02_traceSegment_035_3186_0013, g32p_row02_traceSegment_035_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3213 13 14, g32p_row02_traceSegment_035_3213_0013, g32p_row02_traceSegment_035_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3186 27 27, g32p_row02_traceSegment_035_3186_0027, g32p_row02_traceSegment_035_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3132 54 54, g32p_row02_traceSegment_035_3132_0054, g32p_row02_traceSegment_035_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3024 108 108, g32p_row02_traceSegment_035_3024_0108, g32p_row02_traceSegment_035_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3240 13 14, g32p_row02_traceSegment_035_3240_0013, g32p_row02_traceSegment_035_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3267 13 14, g32p_row02_traceSegment_035_3267_0013, g32p_row02_traceSegment_035_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3240 27 27, g32p_row02_traceSegment_035_3240_0027, g32p_row02_traceSegment_035_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3294 13 14, g32p_row02_traceSegment_035_3294_0013, g32p_row02_traceSegment_035_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3321 13 14, g32p_row02_traceSegment_035_3321_0013, g32p_row02_traceSegment_035_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3294 27 27, g32p_row02_traceSegment_035_3294_0027, g32p_row02_traceSegment_035_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3240 54 54, g32p_row02_traceSegment_035_3240_0054, g32p_row02_traceSegment_035_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3348 13 14, g32p_row02_traceSegment_035_3348_0013, g32p_row02_traceSegment_035_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3375 13 14, g32p_row02_traceSegment_035_3375_0013, g32p_row02_traceSegment_035_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3348 27 27, g32p_row02_traceSegment_035_3348_0027, g32p_row02_traceSegment_035_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3402 13 14, g32p_row02_traceSegment_035_3402_0013, g32p_row02_traceSegment_035_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_035 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_035 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_035_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_035 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3429 13 14, g32p_row02_traceSegment_035_3429_0013, g32p_row02_traceSegment_035_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_035 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3402 27 27, g32p_row02_traceSegment_035_3402_0027, g32p_row02_traceSegment_035_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_035 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3348 54 54, g32p_row02_traceSegment_035_3348_0054, g32p_row02_traceSegment_035_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_035 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3240 108 108, g32p_row02_traceSegment_035_3240_0108, g32p_row02_traceSegment_035_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_035_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_035 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 3024 216 216, g32p_row02_traceSegment_035_3024_0216, g32p_row02_traceSegment_035_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_035_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_035 2592 864 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 2592 432 432, g32p_row02_traceSegment_035_2592_0432, g32p_row02_traceSegment_035_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_035_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_035 1728 1728 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 1728 864 864, g32p_row02_traceSegment_035_1728_0864, g32p_row02_traceSegment_035_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_035_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_035 0 3456 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_035 0 1728 1728, g32p_row02_traceSegment_035_0000_1728, g32p_row02_traceSegment_035_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_035 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 35 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_035_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_037 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 37 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_037_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 13 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 0 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 13 14, g32p_row02_traceSegment_037_0000_0013, g32p_row02_traceSegment_037_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 27 13 14, g32p_row02_traceSegment_037_0027_0013, g32p_row02_traceSegment_037_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 0 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 27 27, g32p_row02_traceSegment_037_0000_0027, g32p_row02_traceSegment_037_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 54 13 14, g32p_row02_traceSegment_037_0054_0013, g32p_row02_traceSegment_037_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 81 13 14, g32p_row02_traceSegment_037_0081_0013, g32p_row02_traceSegment_037_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 54 27 27, g32p_row02_traceSegment_037_0054_0027, g32p_row02_traceSegment_037_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 0 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 54 54, g32p_row02_traceSegment_037_0000_0054, g32p_row02_traceSegment_037_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 108 13 14, g32p_row02_traceSegment_037_0108_0013, g32p_row02_traceSegment_037_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 135 13 14, g32p_row02_traceSegment_037_0135_0013, g32p_row02_traceSegment_037_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 108 27 27, g32p_row02_traceSegment_037_0108_0027, g32p_row02_traceSegment_037_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 162 13 14, g32p_row02_traceSegment_037_0162_0013, g32p_row02_traceSegment_037_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 189 13 14, g32p_row02_traceSegment_037_0189_0013, g32p_row02_traceSegment_037_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 162 27 27, g32p_row02_traceSegment_037_0162_0027, g32p_row02_traceSegment_037_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 108 54 54, g32p_row02_traceSegment_037_0108_0054, g32p_row02_traceSegment_037_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 0 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 108 108, g32p_row02_traceSegment_037_0000_0108, g32p_row02_traceSegment_037_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 216 13 14, g32p_row02_traceSegment_037_0216_0013, g32p_row02_traceSegment_037_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 243 13 14, g32p_row02_traceSegment_037_0243_0013, g32p_row02_traceSegment_037_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 216 27 27, g32p_row02_traceSegment_037_0216_0027, g32p_row02_traceSegment_037_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 270 13 14, g32p_row02_traceSegment_037_0270_0013, g32p_row02_traceSegment_037_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 297 13 14, g32p_row02_traceSegment_037_0297_0013, g32p_row02_traceSegment_037_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 270 27 27, g32p_row02_traceSegment_037_0270_0027, g32p_row02_traceSegment_037_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 216 54 54, g32p_row02_traceSegment_037_0216_0054, g32p_row02_traceSegment_037_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 324 13 14, g32p_row02_traceSegment_037_0324_0013, g32p_row02_traceSegment_037_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 351 13 14, g32p_row02_traceSegment_037_0351_0013, g32p_row02_traceSegment_037_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 324 27 27, g32p_row02_traceSegment_037_0324_0027, g32p_row02_traceSegment_037_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 378 13 14, g32p_row02_traceSegment_037_0378_0013, g32p_row02_traceSegment_037_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 405 13 14, g32p_row02_traceSegment_037_0405_0013, g32p_row02_traceSegment_037_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 378 27 27, g32p_row02_traceSegment_037_0378_0027, g32p_row02_traceSegment_037_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 324 54 54, g32p_row02_traceSegment_037_0324_0054, g32p_row02_traceSegment_037_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 216 108 108, g32p_row02_traceSegment_037_0216_0108, g32p_row02_traceSegment_037_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 0 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 216 216, g32p_row02_traceSegment_037_0000_0216, g32p_row02_traceSegment_037_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 432 13 14, g32p_row02_traceSegment_037_0432_0013, g32p_row02_traceSegment_037_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 459 13 14, g32p_row02_traceSegment_037_0459_0013, g32p_row02_traceSegment_037_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 432 27 27, g32p_row02_traceSegment_037_0432_0027, g32p_row02_traceSegment_037_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 486 13 14, g32p_row02_traceSegment_037_0486_0013, g32p_row02_traceSegment_037_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 513 13 14, g32p_row02_traceSegment_037_0513_0013, g32p_row02_traceSegment_037_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 486 27 27, g32p_row02_traceSegment_037_0486_0027, g32p_row02_traceSegment_037_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 432 54 54, g32p_row02_traceSegment_037_0432_0054, g32p_row02_traceSegment_037_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 540 13 14, g32p_row02_traceSegment_037_0540_0013, g32p_row02_traceSegment_037_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 567 13 14, g32p_row02_traceSegment_037_0567_0013, g32p_row02_traceSegment_037_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 540 27 27, g32p_row02_traceSegment_037_0540_0027, g32p_row02_traceSegment_037_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 594 13 14, g32p_row02_traceSegment_037_0594_0013, g32p_row02_traceSegment_037_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 621 13 14, g32p_row02_traceSegment_037_0621_0013, g32p_row02_traceSegment_037_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 594 27 27, g32p_row02_traceSegment_037_0594_0027, g32p_row02_traceSegment_037_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 540 54 54, g32p_row02_traceSegment_037_0540_0054, g32p_row02_traceSegment_037_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 432 108 108, g32p_row02_traceSegment_037_0432_0108, g32p_row02_traceSegment_037_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 648 13 14, g32p_row02_traceSegment_037_0648_0013, g32p_row02_traceSegment_037_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 675 13 14, g32p_row02_traceSegment_037_0675_0013, g32p_row02_traceSegment_037_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 648 27 27, g32p_row02_traceSegment_037_0648_0027, g32p_row02_traceSegment_037_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 702 13 14, g32p_row02_traceSegment_037_0702_0013, g32p_row02_traceSegment_037_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 729 13 14, g32p_row02_traceSegment_037_0729_0013, g32p_row02_traceSegment_037_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 702 27 27, g32p_row02_traceSegment_037_0702_0027, g32p_row02_traceSegment_037_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 648 54 54, g32p_row02_traceSegment_037_0648_0054, g32p_row02_traceSegment_037_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 756 13 14, g32p_row02_traceSegment_037_0756_0013, g32p_row02_traceSegment_037_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 783 13 14, g32p_row02_traceSegment_037_0783_0013, g32p_row02_traceSegment_037_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 756 27 27, g32p_row02_traceSegment_037_0756_0027, g32p_row02_traceSegment_037_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 810 13 14, g32p_row02_traceSegment_037_0810_0013, g32p_row02_traceSegment_037_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 837 13 14, g32p_row02_traceSegment_037_0837_0013, g32p_row02_traceSegment_037_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 810 27 27, g32p_row02_traceSegment_037_0810_0027, g32p_row02_traceSegment_037_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 756 54 54, g32p_row02_traceSegment_037_0756_0054, g32p_row02_traceSegment_037_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 648 108 108, g32p_row02_traceSegment_037_0648_0108, g32p_row02_traceSegment_037_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 432 216 216, g32p_row02_traceSegment_037_0432_0216, g32p_row02_traceSegment_037_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_037 0 864 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 432 432, g32p_row02_traceSegment_037_0000_0432, g32p_row02_traceSegment_037_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 864 13 14, g32p_row02_traceSegment_037_0864_0013, g32p_row02_traceSegment_037_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 891 13 14, g32p_row02_traceSegment_037_0891_0013, g32p_row02_traceSegment_037_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 864 27 27, g32p_row02_traceSegment_037_0864_0027, g32p_row02_traceSegment_037_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 918 13 14, g32p_row02_traceSegment_037_0918_0013, g32p_row02_traceSegment_037_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 945 13 14, g32p_row02_traceSegment_037_0945_0013, g32p_row02_traceSegment_037_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 918 27 27, g32p_row02_traceSegment_037_0918_0027, g32p_row02_traceSegment_037_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 864 54 54, g32p_row02_traceSegment_037_0864_0054, g32p_row02_traceSegment_037_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 972 13 14, g32p_row02_traceSegment_037_0972_0013, g32p_row02_traceSegment_037_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 999 13 14, g32p_row02_traceSegment_037_0999_0013, g32p_row02_traceSegment_037_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 972 27 27, g32p_row02_traceSegment_037_0972_0027, g32p_row02_traceSegment_037_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1026 13 14, g32p_row02_traceSegment_037_1026_0013, g32p_row02_traceSegment_037_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1053 13 14, g32p_row02_traceSegment_037_1053_0013, g32p_row02_traceSegment_037_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1026 27 27, g32p_row02_traceSegment_037_1026_0027, g32p_row02_traceSegment_037_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 972 54 54, g32p_row02_traceSegment_037_0972_0054, g32p_row02_traceSegment_037_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 864 108 108, g32p_row02_traceSegment_037_0864_0108, g32p_row02_traceSegment_037_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1080 13 14, g32p_row02_traceSegment_037_1080_0013, g32p_row02_traceSegment_037_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1107 13 14, g32p_row02_traceSegment_037_1107_0013, g32p_row02_traceSegment_037_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1080 27 27, g32p_row02_traceSegment_037_1080_0027, g32p_row02_traceSegment_037_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1134 13 14, g32p_row02_traceSegment_037_1134_0013, g32p_row02_traceSegment_037_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1161 13 14, g32p_row02_traceSegment_037_1161_0013, g32p_row02_traceSegment_037_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1134 27 27, g32p_row02_traceSegment_037_1134_0027, g32p_row02_traceSegment_037_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1080 54 54, g32p_row02_traceSegment_037_1080_0054, g32p_row02_traceSegment_037_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1188 13 14, g32p_row02_traceSegment_037_1188_0013, g32p_row02_traceSegment_037_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1215 13 14, g32p_row02_traceSegment_037_1215_0013, g32p_row02_traceSegment_037_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1188 27 27, g32p_row02_traceSegment_037_1188_0027, g32p_row02_traceSegment_037_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1242 13 14, g32p_row02_traceSegment_037_1242_0013, g32p_row02_traceSegment_037_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1269 13 14, g32p_row02_traceSegment_037_1269_0013, g32p_row02_traceSegment_037_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1242 27 27, g32p_row02_traceSegment_037_1242_0027, g32p_row02_traceSegment_037_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1188 54 54, g32p_row02_traceSegment_037_1188_0054, g32p_row02_traceSegment_037_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1080 108 108, g32p_row02_traceSegment_037_1080_0108, g32p_row02_traceSegment_037_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 864 216 216, g32p_row02_traceSegment_037_0864_0216, g32p_row02_traceSegment_037_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1296 13 14, g32p_row02_traceSegment_037_1296_0013, g32p_row02_traceSegment_037_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1323 13 14, g32p_row02_traceSegment_037_1323_0013, g32p_row02_traceSegment_037_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1296 27 27, g32p_row02_traceSegment_037_1296_0027, g32p_row02_traceSegment_037_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1350 13 14, g32p_row02_traceSegment_037_1350_0013, g32p_row02_traceSegment_037_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1377 13 14, g32p_row02_traceSegment_037_1377_0013, g32p_row02_traceSegment_037_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1350 27 27, g32p_row02_traceSegment_037_1350_0027, g32p_row02_traceSegment_037_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1296 54 54, g32p_row02_traceSegment_037_1296_0054, g32p_row02_traceSegment_037_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1404 13 14, g32p_row02_traceSegment_037_1404_0013, g32p_row02_traceSegment_037_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1431 13 14, g32p_row02_traceSegment_037_1431_0013, g32p_row02_traceSegment_037_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1404 27 27, g32p_row02_traceSegment_037_1404_0027, g32p_row02_traceSegment_037_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1458 13 14, g32p_row02_traceSegment_037_1458_0013, g32p_row02_traceSegment_037_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1485 13 14, g32p_row02_traceSegment_037_1485_0013, g32p_row02_traceSegment_037_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1458 27 27, g32p_row02_traceSegment_037_1458_0027, g32p_row02_traceSegment_037_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1404 54 54, g32p_row02_traceSegment_037_1404_0054, g32p_row02_traceSegment_037_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1296 108 108, g32p_row02_traceSegment_037_1296_0108, g32p_row02_traceSegment_037_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1512 13 14, g32p_row02_traceSegment_037_1512_0013, g32p_row02_traceSegment_037_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1539 13 14, g32p_row02_traceSegment_037_1539_0013, g32p_row02_traceSegment_037_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1512 27 27, g32p_row02_traceSegment_037_1512_0027, g32p_row02_traceSegment_037_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1566 13 14, g32p_row02_traceSegment_037_1566_0013, g32p_row02_traceSegment_037_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1593 13 14, g32p_row02_traceSegment_037_1593_0013, g32p_row02_traceSegment_037_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1566 27 27, g32p_row02_traceSegment_037_1566_0027, g32p_row02_traceSegment_037_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1512 54 54, g32p_row02_traceSegment_037_1512_0054, g32p_row02_traceSegment_037_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1620 13 14, g32p_row02_traceSegment_037_1620_0013, g32p_row02_traceSegment_037_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1647 13 14, g32p_row02_traceSegment_037_1647_0013, g32p_row02_traceSegment_037_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1620 27 27, g32p_row02_traceSegment_037_1620_0027, g32p_row02_traceSegment_037_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1674 13 14, g32p_row02_traceSegment_037_1674_0013, g32p_row02_traceSegment_037_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1701 13 14, g32p_row02_traceSegment_037_1701_0013, g32p_row02_traceSegment_037_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1674 27 27, g32p_row02_traceSegment_037_1674_0027, g32p_row02_traceSegment_037_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1620 54 54, g32p_row02_traceSegment_037_1620_0054, g32p_row02_traceSegment_037_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1512 108 108, g32p_row02_traceSegment_037_1512_0108, g32p_row02_traceSegment_037_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1296 216 216, g32p_row02_traceSegment_037_1296_0216, g32p_row02_traceSegment_037_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_037 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 864 432 432, g32p_row02_traceSegment_037_0864_0432, g32p_row02_traceSegment_037_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_037 0 1728 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 864 864, g32p_row02_traceSegment_037_0000_0864, g32p_row02_traceSegment_037_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1728 13 14, g32p_row02_traceSegment_037_1728_0013, g32p_row02_traceSegment_037_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1755 13 14, g32p_row02_traceSegment_037_1755_0013, g32p_row02_traceSegment_037_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1728 27 27, g32p_row02_traceSegment_037_1728_0027, g32p_row02_traceSegment_037_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1782 13 14, g32p_row02_traceSegment_037_1782_0013, g32p_row02_traceSegment_037_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1809 13 14, g32p_row02_traceSegment_037_1809_0013, g32p_row02_traceSegment_037_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1782 27 27, g32p_row02_traceSegment_037_1782_0027, g32p_row02_traceSegment_037_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1728 54 54, g32p_row02_traceSegment_037_1728_0054, g32p_row02_traceSegment_037_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1836 13 14, g32p_row02_traceSegment_037_1836_0013, g32p_row02_traceSegment_037_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1863 13 14, g32p_row02_traceSegment_037_1863_0013, g32p_row02_traceSegment_037_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1836 27 27, g32p_row02_traceSegment_037_1836_0027, g32p_row02_traceSegment_037_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1890 13 14, g32p_row02_traceSegment_037_1890_0013, g32p_row02_traceSegment_037_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1917 13 14, g32p_row02_traceSegment_037_1917_0013, g32p_row02_traceSegment_037_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1890 27 27, g32p_row02_traceSegment_037_1890_0027, g32p_row02_traceSegment_037_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1836 54 54, g32p_row02_traceSegment_037_1836_0054, g32p_row02_traceSegment_037_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1728 108 108, g32p_row02_traceSegment_037_1728_0108, g32p_row02_traceSegment_037_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1944 13 14, g32p_row02_traceSegment_037_1944_0013, g32p_row02_traceSegment_037_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1971 13 14, g32p_row02_traceSegment_037_1971_0013, g32p_row02_traceSegment_037_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1944 27 27, g32p_row02_traceSegment_037_1944_0027, g32p_row02_traceSegment_037_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1998 13 14, g32p_row02_traceSegment_037_1998_0013, g32p_row02_traceSegment_037_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2025 13 14, g32p_row02_traceSegment_037_2025_0013, g32p_row02_traceSegment_037_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1998 27 27, g32p_row02_traceSegment_037_1998_0027, g32p_row02_traceSegment_037_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1944 54 54, g32p_row02_traceSegment_037_1944_0054, g32p_row02_traceSegment_037_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2052 13 14, g32p_row02_traceSegment_037_2052_0013, g32p_row02_traceSegment_037_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2079 13 14, g32p_row02_traceSegment_037_2079_0013, g32p_row02_traceSegment_037_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2052 27 27, g32p_row02_traceSegment_037_2052_0027, g32p_row02_traceSegment_037_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2106 13 14, g32p_row02_traceSegment_037_2106_0013, g32p_row02_traceSegment_037_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2133 13 14, g32p_row02_traceSegment_037_2133_0013, g32p_row02_traceSegment_037_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2106 27 27, g32p_row02_traceSegment_037_2106_0027, g32p_row02_traceSegment_037_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2052 54 54, g32p_row02_traceSegment_037_2052_0054, g32p_row02_traceSegment_037_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1944 108 108, g32p_row02_traceSegment_037_1944_0108, g32p_row02_traceSegment_037_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1728 216 216, g32p_row02_traceSegment_037_1728_0216, g32p_row02_traceSegment_037_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2160 13 14, g32p_row02_traceSegment_037_2160_0013, g32p_row02_traceSegment_037_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2187 13 14, g32p_row02_traceSegment_037_2187_0013, g32p_row02_traceSegment_037_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2160 27 27, g32p_row02_traceSegment_037_2160_0027, g32p_row02_traceSegment_037_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2214 13 14, g32p_row02_traceSegment_037_2214_0013, g32p_row02_traceSegment_037_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2241 13 14, g32p_row02_traceSegment_037_2241_0013, g32p_row02_traceSegment_037_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2214 27 27, g32p_row02_traceSegment_037_2214_0027, g32p_row02_traceSegment_037_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2160 54 54, g32p_row02_traceSegment_037_2160_0054, g32p_row02_traceSegment_037_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2268 13 14, g32p_row02_traceSegment_037_2268_0013, g32p_row02_traceSegment_037_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2295 13 14, g32p_row02_traceSegment_037_2295_0013, g32p_row02_traceSegment_037_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2268 27 27, g32p_row02_traceSegment_037_2268_0027, g32p_row02_traceSegment_037_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2322 13 14, g32p_row02_traceSegment_037_2322_0013, g32p_row02_traceSegment_037_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2349 13 14, g32p_row02_traceSegment_037_2349_0013, g32p_row02_traceSegment_037_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2322 27 27, g32p_row02_traceSegment_037_2322_0027, g32p_row02_traceSegment_037_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2268 54 54, g32p_row02_traceSegment_037_2268_0054, g32p_row02_traceSegment_037_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2160 108 108, g32p_row02_traceSegment_037_2160_0108, g32p_row02_traceSegment_037_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2376 13 14, g32p_row02_traceSegment_037_2376_0013, g32p_row02_traceSegment_037_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2403 13 14, g32p_row02_traceSegment_037_2403_0013, g32p_row02_traceSegment_037_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2376 27 27, g32p_row02_traceSegment_037_2376_0027, g32p_row02_traceSegment_037_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2430 13 14, g32p_row02_traceSegment_037_2430_0013, g32p_row02_traceSegment_037_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2457 13 14, g32p_row02_traceSegment_037_2457_0013, g32p_row02_traceSegment_037_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2430 27 27, g32p_row02_traceSegment_037_2430_0027, g32p_row02_traceSegment_037_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2376 54 54, g32p_row02_traceSegment_037_2376_0054, g32p_row02_traceSegment_037_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2484 13 14, g32p_row02_traceSegment_037_2484_0013, g32p_row02_traceSegment_037_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2511 13 14, g32p_row02_traceSegment_037_2511_0013, g32p_row02_traceSegment_037_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2484 27 27, g32p_row02_traceSegment_037_2484_0027, g32p_row02_traceSegment_037_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2538 13 14, g32p_row02_traceSegment_037_2538_0013, g32p_row02_traceSegment_037_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2565 13 14, g32p_row02_traceSegment_037_2565_0013, g32p_row02_traceSegment_037_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2538 27 27, g32p_row02_traceSegment_037_2538_0027, g32p_row02_traceSegment_037_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2484 54 54, g32p_row02_traceSegment_037_2484_0054, g32p_row02_traceSegment_037_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2376 108 108, g32p_row02_traceSegment_037_2376_0108, g32p_row02_traceSegment_037_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2160 216 216, g32p_row02_traceSegment_037_2160_0216, g32p_row02_traceSegment_037_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1728 432 432, g32p_row02_traceSegment_037_1728_0432, g32p_row02_traceSegment_037_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2592 13 14, g32p_row02_traceSegment_037_2592_0013, g32p_row02_traceSegment_037_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2619 13 14, g32p_row02_traceSegment_037_2619_0013, g32p_row02_traceSegment_037_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2592 27 27, g32p_row02_traceSegment_037_2592_0027, g32p_row02_traceSegment_037_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2646 13 14, g32p_row02_traceSegment_037_2646_0013, g32p_row02_traceSegment_037_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2673 13 14, g32p_row02_traceSegment_037_2673_0013, g32p_row02_traceSegment_037_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2646 27 27, g32p_row02_traceSegment_037_2646_0027, g32p_row02_traceSegment_037_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2592 54 54, g32p_row02_traceSegment_037_2592_0054, g32p_row02_traceSegment_037_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2700 13 14, g32p_row02_traceSegment_037_2700_0013, g32p_row02_traceSegment_037_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2727 13 14, g32p_row02_traceSegment_037_2727_0013, g32p_row02_traceSegment_037_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2700 27 27, g32p_row02_traceSegment_037_2700_0027, g32p_row02_traceSegment_037_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2754 13 14, g32p_row02_traceSegment_037_2754_0013, g32p_row02_traceSegment_037_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2781 13 14, g32p_row02_traceSegment_037_2781_0013, g32p_row02_traceSegment_037_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2754 27 27, g32p_row02_traceSegment_037_2754_0027, g32p_row02_traceSegment_037_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2700 54 54, g32p_row02_traceSegment_037_2700_0054, g32p_row02_traceSegment_037_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2592 108 108, g32p_row02_traceSegment_037_2592_0108, g32p_row02_traceSegment_037_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2808 13 14, g32p_row02_traceSegment_037_2808_0013, g32p_row02_traceSegment_037_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2835 13 14, g32p_row02_traceSegment_037_2835_0013, g32p_row02_traceSegment_037_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2808 27 27, g32p_row02_traceSegment_037_2808_0027, g32p_row02_traceSegment_037_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2862 13 14, g32p_row02_traceSegment_037_2862_0013, g32p_row02_traceSegment_037_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2889 13 14, g32p_row02_traceSegment_037_2889_0013, g32p_row02_traceSegment_037_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2862 27 27, g32p_row02_traceSegment_037_2862_0027, g32p_row02_traceSegment_037_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2808 54 54, g32p_row02_traceSegment_037_2808_0054, g32p_row02_traceSegment_037_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2916 13 14, g32p_row02_traceSegment_037_2916_0013, g32p_row02_traceSegment_037_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2943 13 14, g32p_row02_traceSegment_037_2943_0013, g32p_row02_traceSegment_037_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2916 27 27, g32p_row02_traceSegment_037_2916_0027, g32p_row02_traceSegment_037_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2970 13 14, g32p_row02_traceSegment_037_2970_0013, g32p_row02_traceSegment_037_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2997 13 14, g32p_row02_traceSegment_037_2997_0013, g32p_row02_traceSegment_037_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2970 27 27, g32p_row02_traceSegment_037_2970_0027, g32p_row02_traceSegment_037_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2916 54 54, g32p_row02_traceSegment_037_2916_0054, g32p_row02_traceSegment_037_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2808 108 108, g32p_row02_traceSegment_037_2808_0108, g32p_row02_traceSegment_037_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2592 216 216, g32p_row02_traceSegment_037_2592_0216, g32p_row02_traceSegment_037_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3024 13 14, g32p_row02_traceSegment_037_3024_0013, g32p_row02_traceSegment_037_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3051 13 14, g32p_row02_traceSegment_037_3051_0013, g32p_row02_traceSegment_037_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3024 27 27, g32p_row02_traceSegment_037_3024_0027, g32p_row02_traceSegment_037_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3078 13 14, g32p_row02_traceSegment_037_3078_0013, g32p_row02_traceSegment_037_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3105 13 14, g32p_row02_traceSegment_037_3105_0013, g32p_row02_traceSegment_037_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3078 27 27, g32p_row02_traceSegment_037_3078_0027, g32p_row02_traceSegment_037_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3024 54 54, g32p_row02_traceSegment_037_3024_0054, g32p_row02_traceSegment_037_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3132 13 14, g32p_row02_traceSegment_037_3132_0013, g32p_row02_traceSegment_037_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3159 13 14, g32p_row02_traceSegment_037_3159_0013, g32p_row02_traceSegment_037_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3132 27 27, g32p_row02_traceSegment_037_3132_0027, g32p_row02_traceSegment_037_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3186 13 14, g32p_row02_traceSegment_037_3186_0013, g32p_row02_traceSegment_037_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3213 13 14, g32p_row02_traceSegment_037_3213_0013, g32p_row02_traceSegment_037_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3186 27 27, g32p_row02_traceSegment_037_3186_0027, g32p_row02_traceSegment_037_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3132 54 54, g32p_row02_traceSegment_037_3132_0054, g32p_row02_traceSegment_037_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3024 108 108, g32p_row02_traceSegment_037_3024_0108, g32p_row02_traceSegment_037_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3240 13 14, g32p_row02_traceSegment_037_3240_0013, g32p_row02_traceSegment_037_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3267 13 14, g32p_row02_traceSegment_037_3267_0013, g32p_row02_traceSegment_037_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3240 27 27, g32p_row02_traceSegment_037_3240_0027, g32p_row02_traceSegment_037_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3294 13 14, g32p_row02_traceSegment_037_3294_0013, g32p_row02_traceSegment_037_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3321 13 14, g32p_row02_traceSegment_037_3321_0013, g32p_row02_traceSegment_037_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3294 27 27, g32p_row02_traceSegment_037_3294_0027, g32p_row02_traceSegment_037_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3240 54 54, g32p_row02_traceSegment_037_3240_0054, g32p_row02_traceSegment_037_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3348 13 14, g32p_row02_traceSegment_037_3348_0013, g32p_row02_traceSegment_037_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3375 13 14, g32p_row02_traceSegment_037_3375_0013, g32p_row02_traceSegment_037_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3348 27 27, g32p_row02_traceSegment_037_3348_0027, g32p_row02_traceSegment_037_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3402 13 14, g32p_row02_traceSegment_037_3402_0013, g32p_row02_traceSegment_037_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_037 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_037 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_037_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_037 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3429 13 14, g32p_row02_traceSegment_037_3429_0013, g32p_row02_traceSegment_037_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_037 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3402 27 27, g32p_row02_traceSegment_037_3402_0027, g32p_row02_traceSegment_037_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_037 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3348 54 54, g32p_row02_traceSegment_037_3348_0054, g32p_row02_traceSegment_037_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_037 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3240 108 108, g32p_row02_traceSegment_037_3240_0108, g32p_row02_traceSegment_037_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_037_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_037 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 3024 216 216, g32p_row02_traceSegment_037_3024_0216, g32p_row02_traceSegment_037_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_037_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_037 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 2592 432 432, g32p_row02_traceSegment_037_2592_0432, g32p_row02_traceSegment_037_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_037_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_037 1728 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 1728 864 864, g32p_row02_traceSegment_037_1728_0864, g32p_row02_traceSegment_037_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_037_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_037 0 3456 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_037 0 1728 1728, g32p_row02_traceSegment_037_0000_1728, g32p_row02_traceSegment_037_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_037 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 37 = [0, 0, 0, 0, 1] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_037_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_038 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 38 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_038_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 13 14, g32p_row02_traceSegment_038_0000_0013, g32p_row02_traceSegment_038_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 27 13 14, g32p_row02_traceSegment_038_0027_0013, g32p_row02_traceSegment_038_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 27 27, g32p_row02_traceSegment_038_0000_0027, g32p_row02_traceSegment_038_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 54 13 14, g32p_row02_traceSegment_038_0054_0013, g32p_row02_traceSegment_038_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 81 13 14, g32p_row02_traceSegment_038_0081_0013, g32p_row02_traceSegment_038_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 54 27 27, g32p_row02_traceSegment_038_0054_0027, g32p_row02_traceSegment_038_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 54 54, g32p_row02_traceSegment_038_0000_0054, g32p_row02_traceSegment_038_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 108 13 14, g32p_row02_traceSegment_038_0108_0013, g32p_row02_traceSegment_038_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 135 13 14, g32p_row02_traceSegment_038_0135_0013, g32p_row02_traceSegment_038_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 108 27 27, g32p_row02_traceSegment_038_0108_0027, g32p_row02_traceSegment_038_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 162 13 14, g32p_row02_traceSegment_038_0162_0013, g32p_row02_traceSegment_038_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 189 13 14, g32p_row02_traceSegment_038_0189_0013, g32p_row02_traceSegment_038_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 162 27 27, g32p_row02_traceSegment_038_0162_0027, g32p_row02_traceSegment_038_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 108 54 54, g32p_row02_traceSegment_038_0108_0054, g32p_row02_traceSegment_038_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 108 108, g32p_row02_traceSegment_038_0000_0108, g32p_row02_traceSegment_038_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 216 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 216 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 216 13 14, g32p_row02_traceSegment_038_0216_0013, g32p_row02_traceSegment_038_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 243 13 14, g32p_row02_traceSegment_038_0243_0013, g32p_row02_traceSegment_038_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 216 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 216 27 27, g32p_row02_traceSegment_038_0216_0027, g32p_row02_traceSegment_038_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 283 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 270 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 270 13 14, g32p_row02_traceSegment_038_0270_0013, g32p_row02_traceSegment_038_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 297 13 14, g32p_row02_traceSegment_038_0297_0013, g32p_row02_traceSegment_038_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 270 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 270 27 27, g32p_row02_traceSegment_038_0270_0027, g32p_row02_traceSegment_038_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 216 108 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 216 54 54, g32p_row02_traceSegment_038_0216_0054, g32p_row02_traceSegment_038_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 324 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 324 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 324 13 14, g32p_row02_traceSegment_038_0324_0013, g32p_row02_traceSegment_038_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 351 13 14, g32p_row02_traceSegment_038_0351_0013, g32p_row02_traceSegment_038_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 324 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 324 27 27, g32p_row02_traceSegment_038_0324_0027, g32p_row02_traceSegment_038_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 378 13 14, g32p_row02_traceSegment_038_0378_0013, g32p_row02_traceSegment_038_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 405 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 418 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 405 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 405 13 14, g32p_row02_traceSegment_038_0405_0013, g32p_row02_traceSegment_038_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 378 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 378 27 27, g32p_row02_traceSegment_038_0378_0027, g32p_row02_traceSegment_038_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 324 108 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 324 54 54, g32p_row02_traceSegment_038_0324_0054, g32p_row02_traceSegment_038_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 216 216 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 216 108 108, g32p_row02_traceSegment_038_0216_0108, g32p_row02_traceSegment_038_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 0 432 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 216 216, g32p_row02_traceSegment_038_0000_0216, g32p_row02_traceSegment_038_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 432 13 14, g32p_row02_traceSegment_038_0432_0013, g32p_row02_traceSegment_038_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 459 13 14, g32p_row02_traceSegment_038_0459_0013, g32p_row02_traceSegment_038_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 432 27 27, g32p_row02_traceSegment_038_0432_0027, g32p_row02_traceSegment_038_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 486 13 14, g32p_row02_traceSegment_038_0486_0013, g32p_row02_traceSegment_038_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 513 13 14, g32p_row02_traceSegment_038_0513_0013, g32p_row02_traceSegment_038_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 486 27 27, g32p_row02_traceSegment_038_0486_0027, g32p_row02_traceSegment_038_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 432 54 54, g32p_row02_traceSegment_038_0432_0054, g32p_row02_traceSegment_038_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 540 13 14, g32p_row02_traceSegment_038_0540_0013, g32p_row02_traceSegment_038_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 567 13 14, g32p_row02_traceSegment_038_0567_0013, g32p_row02_traceSegment_038_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 540 27 27, g32p_row02_traceSegment_038_0540_0027, g32p_row02_traceSegment_038_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 594 13 14, g32p_row02_traceSegment_038_0594_0013, g32p_row02_traceSegment_038_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 621 13 14, g32p_row02_traceSegment_038_0621_0013, g32p_row02_traceSegment_038_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 594 27 27, g32p_row02_traceSegment_038_0594_0027, g32p_row02_traceSegment_038_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 540 54 54, g32p_row02_traceSegment_038_0540_0054, g32p_row02_traceSegment_038_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 432 108 108, g32p_row02_traceSegment_038_0432_0108, g32p_row02_traceSegment_038_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 648 13 14, g32p_row02_traceSegment_038_0648_0013, g32p_row02_traceSegment_038_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 675 13 14, g32p_row02_traceSegment_038_0675_0013, g32p_row02_traceSegment_038_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 648 27 27, g32p_row02_traceSegment_038_0648_0027, g32p_row02_traceSegment_038_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 702 13 14, g32p_row02_traceSegment_038_0702_0013, g32p_row02_traceSegment_038_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 729 13 14, g32p_row02_traceSegment_038_0729_0013, g32p_row02_traceSegment_038_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 702 27 27, g32p_row02_traceSegment_038_0702_0027, g32p_row02_traceSegment_038_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 648 54 54, g32p_row02_traceSegment_038_0648_0054, g32p_row02_traceSegment_038_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 756 13 14, g32p_row02_traceSegment_038_0756_0013, g32p_row02_traceSegment_038_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 783 13 14, g32p_row02_traceSegment_038_0783_0013, g32p_row02_traceSegment_038_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 756 27 27, g32p_row02_traceSegment_038_0756_0027, g32p_row02_traceSegment_038_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 810 13 14, g32p_row02_traceSegment_038_0810_0013, g32p_row02_traceSegment_038_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 837 13 14, g32p_row02_traceSegment_038_0837_0013, g32p_row02_traceSegment_038_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 810 27 27, g32p_row02_traceSegment_038_0810_0027, g32p_row02_traceSegment_038_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 756 54 54, g32p_row02_traceSegment_038_0756_0054, g32p_row02_traceSegment_038_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 648 108 108, g32p_row02_traceSegment_038_0648_0108, g32p_row02_traceSegment_038_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 432 216 216, g32p_row02_traceSegment_038_0432_0216, g32p_row02_traceSegment_038_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_038 0 864 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 432 432, g32p_row02_traceSegment_038_0000_0432, g32p_row02_traceSegment_038_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 864 13 14, g32p_row02_traceSegment_038_0864_0013, g32p_row02_traceSegment_038_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 891 13 14, g32p_row02_traceSegment_038_0891_0013, g32p_row02_traceSegment_038_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 864 27 27, g32p_row02_traceSegment_038_0864_0027, g32p_row02_traceSegment_038_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 918 13 14, g32p_row02_traceSegment_038_0918_0013, g32p_row02_traceSegment_038_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 945 13 14, g32p_row02_traceSegment_038_0945_0013, g32p_row02_traceSegment_038_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 918 27 27, g32p_row02_traceSegment_038_0918_0027, g32p_row02_traceSegment_038_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 864 54 54, g32p_row02_traceSegment_038_0864_0054, g32p_row02_traceSegment_038_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 972 13 14, g32p_row02_traceSegment_038_0972_0013, g32p_row02_traceSegment_038_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 999 13 14, g32p_row02_traceSegment_038_0999_0013, g32p_row02_traceSegment_038_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 972 27 27, g32p_row02_traceSegment_038_0972_0027, g32p_row02_traceSegment_038_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1026 13 14, g32p_row02_traceSegment_038_1026_0013, g32p_row02_traceSegment_038_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1053 13 14, g32p_row02_traceSegment_038_1053_0013, g32p_row02_traceSegment_038_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1026 27 27, g32p_row02_traceSegment_038_1026_0027, g32p_row02_traceSegment_038_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 972 54 54, g32p_row02_traceSegment_038_0972_0054, g32p_row02_traceSegment_038_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 864 108 108, g32p_row02_traceSegment_038_0864_0108, g32p_row02_traceSegment_038_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1080 13 14, g32p_row02_traceSegment_038_1080_0013, g32p_row02_traceSegment_038_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1107 13 14, g32p_row02_traceSegment_038_1107_0013, g32p_row02_traceSegment_038_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1080 27 27, g32p_row02_traceSegment_038_1080_0027, g32p_row02_traceSegment_038_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1134 13 14, g32p_row02_traceSegment_038_1134_0013, g32p_row02_traceSegment_038_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1161 13 14, g32p_row02_traceSegment_038_1161_0013, g32p_row02_traceSegment_038_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1134 27 27, g32p_row02_traceSegment_038_1134_0027, g32p_row02_traceSegment_038_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1080 54 54, g32p_row02_traceSegment_038_1080_0054, g32p_row02_traceSegment_038_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1188 13 14, g32p_row02_traceSegment_038_1188_0013, g32p_row02_traceSegment_038_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1215 13 14, g32p_row02_traceSegment_038_1215_0013, g32p_row02_traceSegment_038_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1188 27 27, g32p_row02_traceSegment_038_1188_0027, g32p_row02_traceSegment_038_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1242 13 14, g32p_row02_traceSegment_038_1242_0013, g32p_row02_traceSegment_038_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1269 13 14, g32p_row02_traceSegment_038_1269_0013, g32p_row02_traceSegment_038_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1242 27 27, g32p_row02_traceSegment_038_1242_0027, g32p_row02_traceSegment_038_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1188 54 54, g32p_row02_traceSegment_038_1188_0054, g32p_row02_traceSegment_038_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1080 108 108, g32p_row02_traceSegment_038_1080_0108, g32p_row02_traceSegment_038_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 864 216 216, g32p_row02_traceSegment_038_0864_0216, g32p_row02_traceSegment_038_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1296 13 14, g32p_row02_traceSegment_038_1296_0013, g32p_row02_traceSegment_038_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1323 13 14, g32p_row02_traceSegment_038_1323_0013, g32p_row02_traceSegment_038_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1296 27 27, g32p_row02_traceSegment_038_1296_0027, g32p_row02_traceSegment_038_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1350 13 14, g32p_row02_traceSegment_038_1350_0013, g32p_row02_traceSegment_038_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1377 13 14, g32p_row02_traceSegment_038_1377_0013, g32p_row02_traceSegment_038_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1350 27 27, g32p_row02_traceSegment_038_1350_0027, g32p_row02_traceSegment_038_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1296 54 54, g32p_row02_traceSegment_038_1296_0054, g32p_row02_traceSegment_038_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1404 13 14, g32p_row02_traceSegment_038_1404_0013, g32p_row02_traceSegment_038_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1431 13 14, g32p_row02_traceSegment_038_1431_0013, g32p_row02_traceSegment_038_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1404 27 27, g32p_row02_traceSegment_038_1404_0027, g32p_row02_traceSegment_038_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1458 13 14, g32p_row02_traceSegment_038_1458_0013, g32p_row02_traceSegment_038_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1485 13 14, g32p_row02_traceSegment_038_1485_0013, g32p_row02_traceSegment_038_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1458 27 27, g32p_row02_traceSegment_038_1458_0027, g32p_row02_traceSegment_038_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1404 54 54, g32p_row02_traceSegment_038_1404_0054, g32p_row02_traceSegment_038_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1296 108 108, g32p_row02_traceSegment_038_1296_0108, g32p_row02_traceSegment_038_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1512 13 14, g32p_row02_traceSegment_038_1512_0013, g32p_row02_traceSegment_038_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1539 13 14, g32p_row02_traceSegment_038_1539_0013, g32p_row02_traceSegment_038_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1512 27 27, g32p_row02_traceSegment_038_1512_0027, g32p_row02_traceSegment_038_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1566 13 14, g32p_row02_traceSegment_038_1566_0013, g32p_row02_traceSegment_038_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1593 13 14, g32p_row02_traceSegment_038_1593_0013, g32p_row02_traceSegment_038_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1566 27 27, g32p_row02_traceSegment_038_1566_0027, g32p_row02_traceSegment_038_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1512 54 54, g32p_row02_traceSegment_038_1512_0054, g32p_row02_traceSegment_038_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1620 13 14, g32p_row02_traceSegment_038_1620_0013, g32p_row02_traceSegment_038_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1647 13 14, g32p_row02_traceSegment_038_1647_0013, g32p_row02_traceSegment_038_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1620 27 27, g32p_row02_traceSegment_038_1620_0027, g32p_row02_traceSegment_038_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1674 13 14, g32p_row02_traceSegment_038_1674_0013, g32p_row02_traceSegment_038_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1701 13 14, g32p_row02_traceSegment_038_1701_0013, g32p_row02_traceSegment_038_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1674 27 27, g32p_row02_traceSegment_038_1674_0027, g32p_row02_traceSegment_038_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1620 54 54, g32p_row02_traceSegment_038_1620_0054, g32p_row02_traceSegment_038_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1512 108 108, g32p_row02_traceSegment_038_1512_0108, g32p_row02_traceSegment_038_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1296 216 216, g32p_row02_traceSegment_038_1296_0216, g32p_row02_traceSegment_038_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_038 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 864 432 432, g32p_row02_traceSegment_038_0864_0432, g32p_row02_traceSegment_038_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_038 0 1728 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 864 864, g32p_row02_traceSegment_038_0000_0864, g32p_row02_traceSegment_038_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1728 13 14, g32p_row02_traceSegment_038_1728_0013, g32p_row02_traceSegment_038_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1755 13 14, g32p_row02_traceSegment_038_1755_0013, g32p_row02_traceSegment_038_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1728 27 27, g32p_row02_traceSegment_038_1728_0027, g32p_row02_traceSegment_038_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1782 13 14, g32p_row02_traceSegment_038_1782_0013, g32p_row02_traceSegment_038_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1809 13 14, g32p_row02_traceSegment_038_1809_0013, g32p_row02_traceSegment_038_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1782 27 27, g32p_row02_traceSegment_038_1782_0027, g32p_row02_traceSegment_038_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1728 54 54, g32p_row02_traceSegment_038_1728_0054, g32p_row02_traceSegment_038_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1836 13 14, g32p_row02_traceSegment_038_1836_0013, g32p_row02_traceSegment_038_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1863 13 14, g32p_row02_traceSegment_038_1863_0013, g32p_row02_traceSegment_038_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1836 27 27, g32p_row02_traceSegment_038_1836_0027, g32p_row02_traceSegment_038_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1890 13 14, g32p_row02_traceSegment_038_1890_0013, g32p_row02_traceSegment_038_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1930 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1917 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1917 13 14, g32p_row02_traceSegment_038_1917_0013, g32p_row02_traceSegment_038_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1890 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1890 27 27, g32p_row02_traceSegment_038_1890_0027, g32p_row02_traceSegment_038_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1836 108 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1836 54 54, g32p_row02_traceSegment_038_1836_0054, g32p_row02_traceSegment_038_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 216 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1728 108 108, g32p_row02_traceSegment_038_1728_0108, g32p_row02_traceSegment_038_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1957 14 = [0, 0, 0, 6] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1944 27 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1944 13 14, g32p_row02_traceSegment_038_1944_0013, g32p_row02_traceSegment_038_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1971 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 1984 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1971 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1971 13 14, g32p_row02_traceSegment_038_1971_0013, g32p_row02_traceSegment_038_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1944 54 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1944 27 27, g32p_row02_traceSegment_038_1944_0027, g32p_row02_traceSegment_038_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1998 13 14, g32p_row02_traceSegment_038_1998_0013, g32p_row02_traceSegment_038_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2025 13 14, g32p_row02_traceSegment_038_2025_0013, g32p_row02_traceSegment_038_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1998 27 27, g32p_row02_traceSegment_038_1998_0027, g32p_row02_traceSegment_038_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 1944 108 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1944 54 54, g32p_row02_traceSegment_038_1944_0054, g32p_row02_traceSegment_038_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2065 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2052 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2052 13 14, g32p_row02_traceSegment_038_2052_0013, g32p_row02_traceSegment_038_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2092 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2079 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2079 13 14, g32p_row02_traceSegment_038_2079_0013, g32p_row02_traceSegment_038_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2052 54 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2052 27 27, g32p_row02_traceSegment_038_2052_0027, g32p_row02_traceSegment_038_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2106 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2106 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2106 13 14, g32p_row02_traceSegment_038_2106_0013, g32p_row02_traceSegment_038_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2133 13 14, g32p_row02_traceSegment_038_2133_0013, g32p_row02_traceSegment_038_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2106 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2106 27 27, g32p_row02_traceSegment_038_2106_0027, g32p_row02_traceSegment_038_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2052 108 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2052 54 54, g32p_row02_traceSegment_038_2052_0054, g32p_row02_traceSegment_038_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 1944 216 = [0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1944 108 108, g32p_row02_traceSegment_038_1944_0108, g32p_row02_traceSegment_038_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 432 = [0, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1728 216 216, g32p_row02_traceSegment_038_1728_0216, g32p_row02_traceSegment_038_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2160 13 14, g32p_row02_traceSegment_038_2160_0013, g32p_row02_traceSegment_038_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2187 13 14, g32p_row02_traceSegment_038_2187_0013, g32p_row02_traceSegment_038_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2160 27 27, g32p_row02_traceSegment_038_2160_0027, g32p_row02_traceSegment_038_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2214 13 14, g32p_row02_traceSegment_038_2214_0013, g32p_row02_traceSegment_038_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2241 13 14, g32p_row02_traceSegment_038_2241_0013, g32p_row02_traceSegment_038_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2214 27 27, g32p_row02_traceSegment_038_2214_0027, g32p_row02_traceSegment_038_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2160 54 54, g32p_row02_traceSegment_038_2160_0054, g32p_row02_traceSegment_038_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2281 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2268 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2268 13 14, g32p_row02_traceSegment_038_2268_0013, g32p_row02_traceSegment_038_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2295 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2295 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2295 13 14, g32p_row02_traceSegment_038_2295_0013, g32p_row02_traceSegment_038_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2268 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2268 27 27, g32p_row02_traceSegment_038_2268_0027, g32p_row02_traceSegment_038_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2322 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2322 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2322 13 14, g32p_row02_traceSegment_038_2322_0013, g32p_row02_traceSegment_038_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2349 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2349 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2349 13 14, g32p_row02_traceSegment_038_2349_0013, g32p_row02_traceSegment_038_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2322 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2322 27 27, g32p_row02_traceSegment_038_2322_0027, g32p_row02_traceSegment_038_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2268 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2268 54 54, g32p_row02_traceSegment_038_2268_0054, g32p_row02_traceSegment_038_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 2160 216 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2160 108 108, g32p_row02_traceSegment_038_2160_0108, g32p_row02_traceSegment_038_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2376 13 14, g32p_row02_traceSegment_038_2376_0013, g32p_row02_traceSegment_038_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2403 13 14, g32p_row02_traceSegment_038_2403_0013, g32p_row02_traceSegment_038_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2376 27 27, g32p_row02_traceSegment_038_2376_0027, g32p_row02_traceSegment_038_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2430 13 14, g32p_row02_traceSegment_038_2430_0013, g32p_row02_traceSegment_038_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2457 13 14, g32p_row02_traceSegment_038_2457_0013, g32p_row02_traceSegment_038_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2430 27 27, g32p_row02_traceSegment_038_2430_0027, g32p_row02_traceSegment_038_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2376 54 54, g32p_row02_traceSegment_038_2376_0054, g32p_row02_traceSegment_038_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2484 13 14, g32p_row02_traceSegment_038_2484_0013, g32p_row02_traceSegment_038_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2511 13 14, g32p_row02_traceSegment_038_2511_0013, g32p_row02_traceSegment_038_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2484 27 27, g32p_row02_traceSegment_038_2484_0027, g32p_row02_traceSegment_038_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2538 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2551 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2538 27 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2538 13 14, g32p_row02_traceSegment_038_2538_0013, g32p_row02_traceSegment_038_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2565 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2565 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2565 13 14, g32p_row02_traceSegment_038_2565_0013, g32p_row02_traceSegment_038_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2538 54 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2538 27 27, g32p_row02_traceSegment_038_2538_0027, g32p_row02_traceSegment_038_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2484 108 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2484 54 54, g32p_row02_traceSegment_038_2484_0054, g32p_row02_traceSegment_038_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 2376 216 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2376 108 108, g32p_row02_traceSegment_038_2376_0108, g32p_row02_traceSegment_038_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 2160 432 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2160 216 216, g32p_row02_traceSegment_038_2160_0216, g32p_row02_traceSegment_038_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 864 = [0, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1728 432 432, g32p_row02_traceSegment_038_1728_0432, g32p_row02_traceSegment_038_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2605 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2592 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2592 13 14, g32p_row02_traceSegment_038_2592_0013, g32p_row02_traceSegment_038_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2619 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2632 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2619 27 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2619 13 14, g32p_row02_traceSegment_038_2619_0013, g32p_row02_traceSegment_038_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2592 54 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2592 27 27, g32p_row02_traceSegment_038_2592_0027, g32p_row02_traceSegment_038_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2646 13 14, g32p_row02_traceSegment_038_2646_0013, g32p_row02_traceSegment_038_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2673 13 14, g32p_row02_traceSegment_038_2673_0013, g32p_row02_traceSegment_038_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2646 27 27, g32p_row02_traceSegment_038_2646_0027, g32p_row02_traceSegment_038_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2592 108 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2592 54 54, g32p_row02_traceSegment_038_2592_0054, g32p_row02_traceSegment_038_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2700 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2713 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2700 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2700 13 14, g32p_row02_traceSegment_038_2700_0013, g32p_row02_traceSegment_038_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2727 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2740 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2727 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2727 13 14, g32p_row02_traceSegment_038_2727_0013, g32p_row02_traceSegment_038_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2700 54 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2700 27 27, g32p_row02_traceSegment_038_2700_0027, g32p_row02_traceSegment_038_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2767 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2754 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2754 13 14, g32p_row02_traceSegment_038_2754_0013, g32p_row02_traceSegment_038_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2781 13 = [0, 0, 0, 7] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2794 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2781 27 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2781 13 14, g32p_row02_traceSegment_038_2781_0013, g32p_row02_traceSegment_038_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2754 54 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2754 27 27, g32p_row02_traceSegment_038_2754_0027, g32p_row02_traceSegment_038_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2700 108 = [0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2700 54 54, g32p_row02_traceSegment_038_2700_0054, g32p_row02_traceSegment_038_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 2592 216 = [0, 0, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2592 108 108, g32p_row02_traceSegment_038_2592_0108, g32p_row02_traceSegment_038_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2808 13 = [0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2821 14 = [0, 0, 0, 6] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2808 27 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2808 13 14, g32p_row02_traceSegment_038_2808_0013, g32p_row02_traceSegment_038_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2835 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2848 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2835 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2835 13 14, g32p_row02_traceSegment_038_2835_0013, g32p_row02_traceSegment_038_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2808 54 = [0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2808 27 27, g32p_row02_traceSegment_038_2808_0027, g32p_row02_traceSegment_038_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2862 13 = [0, 0, 0, 6] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2862 27 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2862 13 14, g32p_row02_traceSegment_038_2862_0013, g32p_row02_traceSegment_038_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2889 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2902 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2889 27 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2889 13 14, g32p_row02_traceSegment_038_2889_0013, g32p_row02_traceSegment_038_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2862 54 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2862 27 27, g32p_row02_traceSegment_038_2862_0027, g32p_row02_traceSegment_038_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2808 108 = [0, 0, 0, 29] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2808 54 54, g32p_row02_traceSegment_038_2808_0054, g32p_row02_traceSegment_038_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2916 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2929 14 = [0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2916 27 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2916 13 14, g32p_row02_traceSegment_038_2916_0013, g32p_row02_traceSegment_038_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2943 13 = [0, 0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2956 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2943 27 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2943 13 14, g32p_row02_traceSegment_038_2943_0013, g32p_row02_traceSegment_038_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2916 54 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2916 27 27, g32p_row02_traceSegment_038_2916_0027, g32p_row02_traceSegment_038_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2970 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 2983 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2970 27 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2970 13 14, g32p_row02_traceSegment_038_2970_0013, g32p_row02_traceSegment_038_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 2997 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3010 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 2997 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2997 13 14, g32p_row02_traceSegment_038_2997_0013, g32p_row02_traceSegment_038_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 2970 54 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2970 27 27, g32p_row02_traceSegment_038_2970_0027, g32p_row02_traceSegment_038_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 2916 108 = [0, 0, 0, 21] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2916 54 54, g32p_row02_traceSegment_038_2916_0054, g32p_row02_traceSegment_038_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 2808 216 = [0, 0, 0, 50] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2808 108 108, g32p_row02_traceSegment_038_2808_0108, g32p_row02_traceSegment_038_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 2592 432 = [0, 0, 0, 83] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2592 216 216, g32p_row02_traceSegment_038_2592_0216, g32p_row02_traceSegment_038_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3024 13 14, g32p_row02_traceSegment_038_3024_0013, g32p_row02_traceSegment_038_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3064 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3051 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3051 13 14, g32p_row02_traceSegment_038_3051_0013, g32p_row02_traceSegment_038_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3024 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3024 27 27, g32p_row02_traceSegment_038_3024_0027, g32p_row02_traceSegment_038_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3091 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3078 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3078 13 14, g32p_row02_traceSegment_038_3078_0013, g32p_row02_traceSegment_038_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3105 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3118 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3105 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3105 13 14, g32p_row02_traceSegment_038_3105_0013, g32p_row02_traceSegment_038_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3078 54 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3078 27 27, g32p_row02_traceSegment_038_3078_0027, g32p_row02_traceSegment_038_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 3024 108 = [0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3024 54 54, g32p_row02_traceSegment_038_3024_0054, g32p_row02_traceSegment_038_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3132 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3145 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3132 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3132 13 14, g32p_row02_traceSegment_038_3132_0013, g32p_row02_traceSegment_038_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3159 13 14, g32p_row02_traceSegment_038_3159_0013, g32p_row02_traceSegment_038_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3132 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3132 27 27, g32p_row02_traceSegment_038_3132_0027, g32p_row02_traceSegment_038_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3186 13 14, g32p_row02_traceSegment_038_3186_0013, g32p_row02_traceSegment_038_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3213 13 14, g32p_row02_traceSegment_038_3213_0013, g32p_row02_traceSegment_038_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3186 27 27, g32p_row02_traceSegment_038_3186_0027, g32p_row02_traceSegment_038_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 3132 108 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3132 54 54, g32p_row02_traceSegment_038_3132_0054, g32p_row02_traceSegment_038_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 3024 216 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3024 108 108, g32p_row02_traceSegment_038_3024_0108, g32p_row02_traceSegment_038_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3240 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3240 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3240 13 14, g32p_row02_traceSegment_038_3240_0013, g32p_row02_traceSegment_038_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3267 13 14, g32p_row02_traceSegment_038_3267_0013, g32p_row02_traceSegment_038_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3240 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3240 27 27, g32p_row02_traceSegment_038_3240_0027, g32p_row02_traceSegment_038_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3294 13 14, g32p_row02_traceSegment_038_3294_0013, g32p_row02_traceSegment_038_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3321 13 14, g32p_row02_traceSegment_038_3321_0013, g32p_row02_traceSegment_038_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3294 27 27, g32p_row02_traceSegment_038_3294_0027, g32p_row02_traceSegment_038_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 3240 108 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3240 54 54, g32p_row02_traceSegment_038_3240_0054, g32p_row02_traceSegment_038_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3348 13 14, g32p_row02_traceSegment_038_3348_0013, g32p_row02_traceSegment_038_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3375 13 14, g32p_row02_traceSegment_038_3375_0013, g32p_row02_traceSegment_038_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3348 27 27, g32p_row02_traceSegment_038_3348_0027, g32p_row02_traceSegment_038_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3402 13 14, g32p_row02_traceSegment_038_3402_0013, g32p_row02_traceSegment_038_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_038 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_038 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_038_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_038 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3429 13 14, g32p_row02_traceSegment_038_3429_0013, g32p_row02_traceSegment_038_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_038 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3402 27 27, g32p_row02_traceSegment_038_3402_0027, g32p_row02_traceSegment_038_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_038 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3348 54 54, g32p_row02_traceSegment_038_3348_0054, g32p_row02_traceSegment_038_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_038 3240 216 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3240 108 108, g32p_row02_traceSegment_038_3240_0108, g32p_row02_traceSegment_038_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_038_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_038 3024 432 = [0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 3024 216 216, g32p_row02_traceSegment_038_3024_0216, g32p_row02_traceSegment_038_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_038_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_038 2592 864 = [0, 0, 0, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 2592 432 432, g32p_row02_traceSegment_038_2592_0432, g32p_row02_traceSegment_038_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_038_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_038 1728 1728 = [0, 0, 0, 132] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 1728 864 864, g32p_row02_traceSegment_038_1728_0864, g32p_row02_traceSegment_038_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_038_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_038 0 3456 = [0, 0, 0, 144] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_038 0 1728 1728, g32p_row02_traceSegment_038_0000_1728, g32p_row02_traceSegment_038_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_038 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 38 = [0, 0, 0, 144] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_038_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_040 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 40 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_040_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 13 14, g32p_row02_traceSegment_040_0000_0013, g32p_row02_traceSegment_040_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 27 13 14, g32p_row02_traceSegment_040_0027_0013, g32p_row02_traceSegment_040_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 27 27, g32p_row02_traceSegment_040_0000_0027, g32p_row02_traceSegment_040_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 54 13 14, g32p_row02_traceSegment_040_0054_0013, g32p_row02_traceSegment_040_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 81 13 14, g32p_row02_traceSegment_040_0081_0013, g32p_row02_traceSegment_040_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 54 27 27, g32p_row02_traceSegment_040_0054_0027, g32p_row02_traceSegment_040_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 54 54, g32p_row02_traceSegment_040_0000_0054, g32p_row02_traceSegment_040_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 108 13 14, g32p_row02_traceSegment_040_0108_0013, g32p_row02_traceSegment_040_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 135 13 14, g32p_row02_traceSegment_040_0135_0013, g32p_row02_traceSegment_040_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 108 27 27, g32p_row02_traceSegment_040_0108_0027, g32p_row02_traceSegment_040_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 162 13 14, g32p_row02_traceSegment_040_0162_0013, g32p_row02_traceSegment_040_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 189 13 14, g32p_row02_traceSegment_040_0189_0013, g32p_row02_traceSegment_040_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 162 27 27, g32p_row02_traceSegment_040_0162_0027, g32p_row02_traceSegment_040_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 108 54 54, g32p_row02_traceSegment_040_0108_0054, g32p_row02_traceSegment_040_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 108 108, g32p_row02_traceSegment_040_0000_0108, g32p_row02_traceSegment_040_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 216 13 14, g32p_row02_traceSegment_040_0216_0013, g32p_row02_traceSegment_040_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 243 13 14, g32p_row02_traceSegment_040_0243_0013, g32p_row02_traceSegment_040_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 216 27 27, g32p_row02_traceSegment_040_0216_0027, g32p_row02_traceSegment_040_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 270 13 14, g32p_row02_traceSegment_040_0270_0013, g32p_row02_traceSegment_040_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 297 13 14, g32p_row02_traceSegment_040_0297_0013, g32p_row02_traceSegment_040_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 270 27 27, g32p_row02_traceSegment_040_0270_0027, g32p_row02_traceSegment_040_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 216 54 54, g32p_row02_traceSegment_040_0216_0054, g32p_row02_traceSegment_040_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 324 13 14, g32p_row02_traceSegment_040_0324_0013, g32p_row02_traceSegment_040_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 351 13 14, g32p_row02_traceSegment_040_0351_0013, g32p_row02_traceSegment_040_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 324 27 27, g32p_row02_traceSegment_040_0324_0027, g32p_row02_traceSegment_040_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 378 13 14, g32p_row02_traceSegment_040_0378_0013, g32p_row02_traceSegment_040_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 405 13 14, g32p_row02_traceSegment_040_0405_0013, g32p_row02_traceSegment_040_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 378 27 27, g32p_row02_traceSegment_040_0378_0027, g32p_row02_traceSegment_040_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 324 54 54, g32p_row02_traceSegment_040_0324_0054, g32p_row02_traceSegment_040_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 216 108 108, g32p_row02_traceSegment_040_0216_0108, g32p_row02_traceSegment_040_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 216 216, g32p_row02_traceSegment_040_0000_0216, g32p_row02_traceSegment_040_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 432 13 14, g32p_row02_traceSegment_040_0432_0013, g32p_row02_traceSegment_040_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 459 13 14, g32p_row02_traceSegment_040_0459_0013, g32p_row02_traceSegment_040_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 432 27 27, g32p_row02_traceSegment_040_0432_0027, g32p_row02_traceSegment_040_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 486 13 14, g32p_row02_traceSegment_040_0486_0013, g32p_row02_traceSegment_040_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 513 13 14, g32p_row02_traceSegment_040_0513_0013, g32p_row02_traceSegment_040_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 486 27 27, g32p_row02_traceSegment_040_0486_0027, g32p_row02_traceSegment_040_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 432 54 54, g32p_row02_traceSegment_040_0432_0054, g32p_row02_traceSegment_040_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 540 13 14, g32p_row02_traceSegment_040_0540_0013, g32p_row02_traceSegment_040_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 567 13 14, g32p_row02_traceSegment_040_0567_0013, g32p_row02_traceSegment_040_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 540 27 27, g32p_row02_traceSegment_040_0540_0027, g32p_row02_traceSegment_040_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 594 13 14, g32p_row02_traceSegment_040_0594_0013, g32p_row02_traceSegment_040_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 621 13 14, g32p_row02_traceSegment_040_0621_0013, g32p_row02_traceSegment_040_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 594 27 27, g32p_row02_traceSegment_040_0594_0027, g32p_row02_traceSegment_040_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 540 54 54, g32p_row02_traceSegment_040_0540_0054, g32p_row02_traceSegment_040_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 432 108 108, g32p_row02_traceSegment_040_0432_0108, g32p_row02_traceSegment_040_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 648 13 14, g32p_row02_traceSegment_040_0648_0013, g32p_row02_traceSegment_040_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 675 13 14, g32p_row02_traceSegment_040_0675_0013, g32p_row02_traceSegment_040_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 648 27 27, g32p_row02_traceSegment_040_0648_0027, g32p_row02_traceSegment_040_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 702 13 14, g32p_row02_traceSegment_040_0702_0013, g32p_row02_traceSegment_040_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 729 13 14, g32p_row02_traceSegment_040_0729_0013, g32p_row02_traceSegment_040_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 702 27 27, g32p_row02_traceSegment_040_0702_0027, g32p_row02_traceSegment_040_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 648 54 54, g32p_row02_traceSegment_040_0648_0054, g32p_row02_traceSegment_040_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 756 13 14, g32p_row02_traceSegment_040_0756_0013, g32p_row02_traceSegment_040_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 783 13 14, g32p_row02_traceSegment_040_0783_0013, g32p_row02_traceSegment_040_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 756 27 27, g32p_row02_traceSegment_040_0756_0027, g32p_row02_traceSegment_040_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 810 13 14, g32p_row02_traceSegment_040_0810_0013, g32p_row02_traceSegment_040_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 837 13 14, g32p_row02_traceSegment_040_0837_0013, g32p_row02_traceSegment_040_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 810 27 27, g32p_row02_traceSegment_040_0810_0027, g32p_row02_traceSegment_040_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 756 54 54, g32p_row02_traceSegment_040_0756_0054, g32p_row02_traceSegment_040_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 648 108 108, g32p_row02_traceSegment_040_0648_0108, g32p_row02_traceSegment_040_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 432 216 216, g32p_row02_traceSegment_040_0432_0216, g32p_row02_traceSegment_040_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_040 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 432 432, g32p_row02_traceSegment_040_0000_0432, g32p_row02_traceSegment_040_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 864 13 14, g32p_row02_traceSegment_040_0864_0013, g32p_row02_traceSegment_040_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 891 13 14, g32p_row02_traceSegment_040_0891_0013, g32p_row02_traceSegment_040_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 864 27 27, g32p_row02_traceSegment_040_0864_0027, g32p_row02_traceSegment_040_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 918 13 14, g32p_row02_traceSegment_040_0918_0013, g32p_row02_traceSegment_040_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 945 13 14, g32p_row02_traceSegment_040_0945_0013, g32p_row02_traceSegment_040_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 918 27 27, g32p_row02_traceSegment_040_0918_0027, g32p_row02_traceSegment_040_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 864 54 54, g32p_row02_traceSegment_040_0864_0054, g32p_row02_traceSegment_040_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 972 13 14, g32p_row02_traceSegment_040_0972_0013, g32p_row02_traceSegment_040_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 999 13 14, g32p_row02_traceSegment_040_0999_0013, g32p_row02_traceSegment_040_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 972 27 27, g32p_row02_traceSegment_040_0972_0027, g32p_row02_traceSegment_040_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1026 13 14, g32p_row02_traceSegment_040_1026_0013, g32p_row02_traceSegment_040_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1053 13 14, g32p_row02_traceSegment_040_1053_0013, g32p_row02_traceSegment_040_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1026 27 27, g32p_row02_traceSegment_040_1026_0027, g32p_row02_traceSegment_040_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 972 54 54, g32p_row02_traceSegment_040_0972_0054, g32p_row02_traceSegment_040_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 864 108 108, g32p_row02_traceSegment_040_0864_0108, g32p_row02_traceSegment_040_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1080 13 14, g32p_row02_traceSegment_040_1080_0013, g32p_row02_traceSegment_040_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1107 13 14, g32p_row02_traceSegment_040_1107_0013, g32p_row02_traceSegment_040_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1080 27 27, g32p_row02_traceSegment_040_1080_0027, g32p_row02_traceSegment_040_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1134 13 14, g32p_row02_traceSegment_040_1134_0013, g32p_row02_traceSegment_040_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1161 13 14, g32p_row02_traceSegment_040_1161_0013, g32p_row02_traceSegment_040_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1134 27 27, g32p_row02_traceSegment_040_1134_0027, g32p_row02_traceSegment_040_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1080 54 54, g32p_row02_traceSegment_040_1080_0054, g32p_row02_traceSegment_040_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1188 13 14, g32p_row02_traceSegment_040_1188_0013, g32p_row02_traceSegment_040_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1215 13 14, g32p_row02_traceSegment_040_1215_0013, g32p_row02_traceSegment_040_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1188 27 27, g32p_row02_traceSegment_040_1188_0027, g32p_row02_traceSegment_040_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1242 13 14, g32p_row02_traceSegment_040_1242_0013, g32p_row02_traceSegment_040_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1269 13 14, g32p_row02_traceSegment_040_1269_0013, g32p_row02_traceSegment_040_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1242 27 27, g32p_row02_traceSegment_040_1242_0027, g32p_row02_traceSegment_040_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1188 54 54, g32p_row02_traceSegment_040_1188_0054, g32p_row02_traceSegment_040_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1080 108 108, g32p_row02_traceSegment_040_1080_0108, g32p_row02_traceSegment_040_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 864 216 216, g32p_row02_traceSegment_040_0864_0216, g32p_row02_traceSegment_040_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1296 13 14, g32p_row02_traceSegment_040_1296_0013, g32p_row02_traceSegment_040_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1323 13 14, g32p_row02_traceSegment_040_1323_0013, g32p_row02_traceSegment_040_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1296 27 27, g32p_row02_traceSegment_040_1296_0027, g32p_row02_traceSegment_040_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1350 13 14, g32p_row02_traceSegment_040_1350_0013, g32p_row02_traceSegment_040_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1377 13 14, g32p_row02_traceSegment_040_1377_0013, g32p_row02_traceSegment_040_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1350 27 27, g32p_row02_traceSegment_040_1350_0027, g32p_row02_traceSegment_040_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1296 54 54, g32p_row02_traceSegment_040_1296_0054, g32p_row02_traceSegment_040_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1404 13 14, g32p_row02_traceSegment_040_1404_0013, g32p_row02_traceSegment_040_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1431 13 14, g32p_row02_traceSegment_040_1431_0013, g32p_row02_traceSegment_040_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1404 27 27, g32p_row02_traceSegment_040_1404_0027, g32p_row02_traceSegment_040_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1458 13 14, g32p_row02_traceSegment_040_1458_0013, g32p_row02_traceSegment_040_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1485 13 14, g32p_row02_traceSegment_040_1485_0013, g32p_row02_traceSegment_040_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1458 27 27, g32p_row02_traceSegment_040_1458_0027, g32p_row02_traceSegment_040_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1404 54 54, g32p_row02_traceSegment_040_1404_0054, g32p_row02_traceSegment_040_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1296 108 108, g32p_row02_traceSegment_040_1296_0108, g32p_row02_traceSegment_040_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1512 13 14, g32p_row02_traceSegment_040_1512_0013, g32p_row02_traceSegment_040_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1539 13 14, g32p_row02_traceSegment_040_1539_0013, g32p_row02_traceSegment_040_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1512 27 27, g32p_row02_traceSegment_040_1512_0027, g32p_row02_traceSegment_040_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1566 13 14, g32p_row02_traceSegment_040_1566_0013, g32p_row02_traceSegment_040_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1593 13 14, g32p_row02_traceSegment_040_1593_0013, g32p_row02_traceSegment_040_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1566 27 27, g32p_row02_traceSegment_040_1566_0027, g32p_row02_traceSegment_040_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1512 54 54, g32p_row02_traceSegment_040_1512_0054, g32p_row02_traceSegment_040_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1620 13 14, g32p_row02_traceSegment_040_1620_0013, g32p_row02_traceSegment_040_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1647 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1660 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1647 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1647 13 14, g32p_row02_traceSegment_040_1647_0013, g32p_row02_traceSegment_040_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1620 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1620 27 27, g32p_row02_traceSegment_040_1620_0027, g32p_row02_traceSegment_040_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1674 13 14, g32p_row02_traceSegment_040_1674_0013, g32p_row02_traceSegment_040_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1701 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1701 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1701 13 14, g32p_row02_traceSegment_040_1701_0013, g32p_row02_traceSegment_040_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1674 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1674 27 27, g32p_row02_traceSegment_040_1674_0027, g32p_row02_traceSegment_040_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1620 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1620 54 54, g32p_row02_traceSegment_040_1620_0054, g32p_row02_traceSegment_040_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 1512 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1512 108 108, g32p_row02_traceSegment_040_1512_0108, g32p_row02_traceSegment_040_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 1296 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1296 216 216, g32p_row02_traceSegment_040_1296_0216, g32p_row02_traceSegment_040_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_040 864 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 864 432 432, g32p_row02_traceSegment_040_0864_0432, g32p_row02_traceSegment_040_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_040 0 1728 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 864 864, g32p_row02_traceSegment_040_0000_0864, g32p_row02_traceSegment_040_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1728 13 14, g32p_row02_traceSegment_040_1728_0013, g32p_row02_traceSegment_040_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1755 13 14, g32p_row02_traceSegment_040_1755_0013, g32p_row02_traceSegment_040_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1728 27 27, g32p_row02_traceSegment_040_1728_0027, g32p_row02_traceSegment_040_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1782 13 14, g32p_row02_traceSegment_040_1782_0013, g32p_row02_traceSegment_040_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1809 13 14, g32p_row02_traceSegment_040_1809_0013, g32p_row02_traceSegment_040_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1782 27 27, g32p_row02_traceSegment_040_1782_0027, g32p_row02_traceSegment_040_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1728 54 54, g32p_row02_traceSegment_040_1728_0054, g32p_row02_traceSegment_040_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1836 13 14, g32p_row02_traceSegment_040_1836_0013, g32p_row02_traceSegment_040_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1863 13 14, g32p_row02_traceSegment_040_1863_0013, g32p_row02_traceSegment_040_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1836 27 27, g32p_row02_traceSegment_040_1836_0027, g32p_row02_traceSegment_040_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1890 13 14, g32p_row02_traceSegment_040_1890_0013, g32p_row02_traceSegment_040_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1930 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1917 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1917 13 14, g32p_row02_traceSegment_040_1917_0013, g32p_row02_traceSegment_040_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1890 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1890 27 27, g32p_row02_traceSegment_040_1890_0027, g32p_row02_traceSegment_040_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1836 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1836 54 54, g32p_row02_traceSegment_040_1836_0054, g32p_row02_traceSegment_040_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1728 108 108, g32p_row02_traceSegment_040_1728_0108, g32p_row02_traceSegment_040_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1944 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1957 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1944 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1944 13 14, g32p_row02_traceSegment_040_1944_0013, g32p_row02_traceSegment_040_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1971 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 1984 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1971 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1971 13 14, g32p_row02_traceSegment_040_1971_0013, g32p_row02_traceSegment_040_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1944 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1944 27 27, g32p_row02_traceSegment_040_1944_0027, g32p_row02_traceSegment_040_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 1998 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2011 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 1998 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1998 13 14, g32p_row02_traceSegment_040_1998_0013, g32p_row02_traceSegment_040_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2038 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2025 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2025 13 14, g32p_row02_traceSegment_040_2025_0013, g32p_row02_traceSegment_040_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 1998 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1998 27 27, g32p_row02_traceSegment_040_1998_0027, g32p_row02_traceSegment_040_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 1944 108 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1944 54 54, g32p_row02_traceSegment_040_1944_0054, g32p_row02_traceSegment_040_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2052 13 14, g32p_row02_traceSegment_040_2052_0013, g32p_row02_traceSegment_040_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2079 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2092 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2079 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2079 13 14, g32p_row02_traceSegment_040_2079_0013, g32p_row02_traceSegment_040_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2052 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2052 27 27, g32p_row02_traceSegment_040_2052_0027, g32p_row02_traceSegment_040_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2119 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2106 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2106 13 14, g32p_row02_traceSegment_040_2106_0013, g32p_row02_traceSegment_040_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2146 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2133 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2133 13 14, g32p_row02_traceSegment_040_2133_0013, g32p_row02_traceSegment_040_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2106 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2106 27 27, g32p_row02_traceSegment_040_2106_0027, g32p_row02_traceSegment_040_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2052 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2052 54 54, g32p_row02_traceSegment_040_2052_0054, g32p_row02_traceSegment_040_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 1944 216 = [11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1944 108 108, g32p_row02_traceSegment_040_1944_0108, g32p_row02_traceSegment_040_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 432 = [13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1728 216 216, g32p_row02_traceSegment_040_1728_0216, g32p_row02_traceSegment_040_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2160 13 14, g32p_row02_traceSegment_040_2160_0013, g32p_row02_traceSegment_040_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2187 13 14, g32p_row02_traceSegment_040_2187_0013, g32p_row02_traceSegment_040_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2160 27 27, g32p_row02_traceSegment_040_2160_0027, g32p_row02_traceSegment_040_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2214 13 14, g32p_row02_traceSegment_040_2214_0013, g32p_row02_traceSegment_040_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2241 13 14, g32p_row02_traceSegment_040_2241_0013, g32p_row02_traceSegment_040_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2214 27 27, g32p_row02_traceSegment_040_2214_0027, g32p_row02_traceSegment_040_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2160 54 54, g32p_row02_traceSegment_040_2160_0054, g32p_row02_traceSegment_040_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2268 13 14, g32p_row02_traceSegment_040_2268_0013, g32p_row02_traceSegment_040_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2295 13 14, g32p_row02_traceSegment_040_2295_0013, g32p_row02_traceSegment_040_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2268 27 27, g32p_row02_traceSegment_040_2268_0027, g32p_row02_traceSegment_040_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2322 13 14, g32p_row02_traceSegment_040_2322_0013, g32p_row02_traceSegment_040_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2349 13 14, g32p_row02_traceSegment_040_2349_0013, g32p_row02_traceSegment_040_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2322 27 27, g32p_row02_traceSegment_040_2322_0027, g32p_row02_traceSegment_040_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2268 54 54, g32p_row02_traceSegment_040_2268_0054, g32p_row02_traceSegment_040_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2160 108 108, g32p_row02_traceSegment_040_2160_0108, g32p_row02_traceSegment_040_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2376 13 14, g32p_row02_traceSegment_040_2376_0013, g32p_row02_traceSegment_040_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2403 13 14, g32p_row02_traceSegment_040_2403_0013, g32p_row02_traceSegment_040_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2376 27 27, g32p_row02_traceSegment_040_2376_0027, g32p_row02_traceSegment_040_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2430 13 14, g32p_row02_traceSegment_040_2430_0013, g32p_row02_traceSegment_040_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2457 13 14, g32p_row02_traceSegment_040_2457_0013, g32p_row02_traceSegment_040_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2430 27 27, g32p_row02_traceSegment_040_2430_0027, g32p_row02_traceSegment_040_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2376 54 54, g32p_row02_traceSegment_040_2376_0054, g32p_row02_traceSegment_040_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2484 13 14, g32p_row02_traceSegment_040_2484_0013, g32p_row02_traceSegment_040_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2511 13 14, g32p_row02_traceSegment_040_2511_0013, g32p_row02_traceSegment_040_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2484 27 27, g32p_row02_traceSegment_040_2484_0027, g32p_row02_traceSegment_040_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2538 13 14, g32p_row02_traceSegment_040_2538_0013, g32p_row02_traceSegment_040_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2578 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2565 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2565 13 14, g32p_row02_traceSegment_040_2565_0013, g32p_row02_traceSegment_040_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2538 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2538 27 27, g32p_row02_traceSegment_040_2538_0027, g32p_row02_traceSegment_040_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2484 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2484 54 54, g32p_row02_traceSegment_040_2484_0054, g32p_row02_traceSegment_040_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 2376 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2376 108 108, g32p_row02_traceSegment_040_2376_0108, g32p_row02_traceSegment_040_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 2160 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2160 216 216, g32p_row02_traceSegment_040_2160_0216, g32p_row02_traceSegment_040_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 864 = [15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1728 432 432, g32p_row02_traceSegment_040_1728_0432, g32p_row02_traceSegment_040_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2592 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2592 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2592 13 14, g32p_row02_traceSegment_040_2592_0013, g32p_row02_traceSegment_040_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2632 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2619 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2619 13 14, g32p_row02_traceSegment_040_2619_0013, g32p_row02_traceSegment_040_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2592 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2592 27 27, g32p_row02_traceSegment_040_2592_0027, g32p_row02_traceSegment_040_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2646 13 14, g32p_row02_traceSegment_040_2646_0013, g32p_row02_traceSegment_040_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2673 13 14, g32p_row02_traceSegment_040_2673_0013, g32p_row02_traceSegment_040_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2646 27 27, g32p_row02_traceSegment_040_2646_0027, g32p_row02_traceSegment_040_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2592 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2592 54 54, g32p_row02_traceSegment_040_2592_0054, g32p_row02_traceSegment_040_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2700 13 14, g32p_row02_traceSegment_040_2700_0013, g32p_row02_traceSegment_040_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2727 13 14, g32p_row02_traceSegment_040_2727_0013, g32p_row02_traceSegment_040_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2700 27 27, g32p_row02_traceSegment_040_2700_0027, g32p_row02_traceSegment_040_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2754 13 14, g32p_row02_traceSegment_040_2754_0013, g32p_row02_traceSegment_040_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2781 13 14, g32p_row02_traceSegment_040_2781_0013, g32p_row02_traceSegment_040_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2754 27 27, g32p_row02_traceSegment_040_2754_0027, g32p_row02_traceSegment_040_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2700 54 54, g32p_row02_traceSegment_040_2700_0054, g32p_row02_traceSegment_040_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 2592 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2592 108 108, g32p_row02_traceSegment_040_2592_0108, g32p_row02_traceSegment_040_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2808 13 14, g32p_row02_traceSegment_040_2808_0013, g32p_row02_traceSegment_040_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2835 13 14, g32p_row02_traceSegment_040_2835_0013, g32p_row02_traceSegment_040_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2808 27 27, g32p_row02_traceSegment_040_2808_0027, g32p_row02_traceSegment_040_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2862 13 14, g32p_row02_traceSegment_040_2862_0013, g32p_row02_traceSegment_040_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2889 13 14, g32p_row02_traceSegment_040_2889_0013, g32p_row02_traceSegment_040_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2862 27 27, g32p_row02_traceSegment_040_2862_0027, g32p_row02_traceSegment_040_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2808 54 54, g32p_row02_traceSegment_040_2808_0054, g32p_row02_traceSegment_040_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2916 13 14, g32p_row02_traceSegment_040_2916_0013, g32p_row02_traceSegment_040_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2956 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2943 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2943 13 14, g32p_row02_traceSegment_040_2943_0013, g32p_row02_traceSegment_040_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2916 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2916 27 27, g32p_row02_traceSegment_040_2916_0027, g32p_row02_traceSegment_040_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2970 13 14, g32p_row02_traceSegment_040_2970_0013, g32p_row02_traceSegment_040_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2997 13 14, g32p_row02_traceSegment_040_2997_0013, g32p_row02_traceSegment_040_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2970 27 27, g32p_row02_traceSegment_040_2970_0027, g32p_row02_traceSegment_040_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 2916 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2916 54 54, g32p_row02_traceSegment_040_2916_0054, g32p_row02_traceSegment_040_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 2808 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2808 108 108, g32p_row02_traceSegment_040_2808_0108, g32p_row02_traceSegment_040_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 2592 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2592 216 216, g32p_row02_traceSegment_040_2592_0216, g32p_row02_traceSegment_040_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3024 13 14, g32p_row02_traceSegment_040_3024_0013, g32p_row02_traceSegment_040_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3051 13 14, g32p_row02_traceSegment_040_3051_0013, g32p_row02_traceSegment_040_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3024 27 27, g32p_row02_traceSegment_040_3024_0027, g32p_row02_traceSegment_040_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3078 13 14, g32p_row02_traceSegment_040_3078_0013, g32p_row02_traceSegment_040_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3105 13 14, g32p_row02_traceSegment_040_3105_0013, g32p_row02_traceSegment_040_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3078 27 27, g32p_row02_traceSegment_040_3078_0027, g32p_row02_traceSegment_040_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3024 54 54, g32p_row02_traceSegment_040_3024_0054, g32p_row02_traceSegment_040_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3132 13 14, g32p_row02_traceSegment_040_3132_0013, g32p_row02_traceSegment_040_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3159 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3172 14 = [4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3159 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3159 13 14, g32p_row02_traceSegment_040_3159_0013, g32p_row02_traceSegment_040_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3132 54 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3132 27 27, g32p_row02_traceSegment_040_3132_0027, g32p_row02_traceSegment_040_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3186 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3186 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3186 13 14, g32p_row02_traceSegment_040_3186_0013, g32p_row02_traceSegment_040_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3213 13 14, g32p_row02_traceSegment_040_3213_0013, g32p_row02_traceSegment_040_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3186 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3186 27 27, g32p_row02_traceSegment_040_3186_0027, g32p_row02_traceSegment_040_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 3132 108 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3132 54 54, g32p_row02_traceSegment_040_3132_0054, g32p_row02_traceSegment_040_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 3024 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3024 108 108, g32p_row02_traceSegment_040_3024_0108, g32p_row02_traceSegment_040_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3240 13 14, g32p_row02_traceSegment_040_3240_0013, g32p_row02_traceSegment_040_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3267 13 14, g32p_row02_traceSegment_040_3267_0013, g32p_row02_traceSegment_040_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3240 27 27, g32p_row02_traceSegment_040_3240_0027, g32p_row02_traceSegment_040_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3294 13 14, g32p_row02_traceSegment_040_3294_0013, g32p_row02_traceSegment_040_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3321 13 14, g32p_row02_traceSegment_040_3321_0013, g32p_row02_traceSegment_040_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3294 27 27, g32p_row02_traceSegment_040_3294_0027, g32p_row02_traceSegment_040_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3240 54 54, g32p_row02_traceSegment_040_3240_0054, g32p_row02_traceSegment_040_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3348 13 14, g32p_row02_traceSegment_040_3348_0013, g32p_row02_traceSegment_040_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3375 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3388 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3375 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3375 13 14, g32p_row02_traceSegment_040_3375_0013, g32p_row02_traceSegment_040_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3348 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3348 27 27, g32p_row02_traceSegment_040_3348_0027, g32p_row02_traceSegment_040_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3415 14 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3402 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3402 13 14, g32p_row02_traceSegment_040_3402_0013, g32p_row02_traceSegment_040_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_040 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_040 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_040_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_040 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3429 13 14, g32p_row02_traceSegment_040_3429_0013, g32p_row02_traceSegment_040_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_040 3402 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3402 27 27, g32p_row02_traceSegment_040_3402_0027, g32p_row02_traceSegment_040_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_040 3348 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3348 54 54, g32p_row02_traceSegment_040_3348_0054, g32p_row02_traceSegment_040_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_040 3240 216 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3240 108 108, g32p_row02_traceSegment_040_3240_0108, g32p_row02_traceSegment_040_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_040_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_040 3024 432 = [11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 3024 216 216, g32p_row02_traceSegment_040_3024_0216, g32p_row02_traceSegment_040_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_040_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_040 2592 864 = [14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 2592 432 432, g32p_row02_traceSegment_040_2592_0432, g32p_row02_traceSegment_040_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_040_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_040 1728 1728 = [29] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 1728 864 864, g32p_row02_traceSegment_040_1728_0864, g32p_row02_traceSegment_040_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_040_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_040 0 3456 = [32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_040 0 1728 1728, g32p_row02_traceSegment_040_0000_1728, g32p_row02_traceSegment_040_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_040 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 40 = [32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_040_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_030 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 30) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 30) (g32p_literalTraceValue 1 30)
      [1, -1, 1] [3456, 3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_030]
  decide +kernel

theorem g32p_row02_tracePolynomial_031 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 31) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 31) (g32p_literalTraceValue 1 31)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_031]
  decide +kernel

theorem g32p_row02_tracePolynomial_032 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 32) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 32) (g32p_literalTraceValue 1 32)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_032]
  decide +kernel

theorem g32p_row02_tracePolynomial_034 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 34) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 34) (g32p_literalTraceValue 1 34)
      [1, -1, 1] [3456, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_034]
  decide +kernel

theorem g32p_row02_tracePolynomial_035 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 35) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 35) (g32p_literalTraceValue 1 35)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_035]
  decide +kernel

theorem g32p_row02_tracePolynomial_037 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 37) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 37) (g32p_literalTraceValue 1 37)
      [1, -1, 1] [155520, 155520, 155520] = true := by
  rw [g32p_row02_traceCoefficients_037]
  decide +kernel

theorem g32p_row02_tracePolynomial_038 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 38) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 38) (g32p_literalTraceValue 1 38)
      [1, -1, 1] [3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_038]
  decide +kernel

theorem g32p_row02_tracePolynomial_040 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 40) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 40) (g32p_literalTraceValue 1 40)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_040]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
