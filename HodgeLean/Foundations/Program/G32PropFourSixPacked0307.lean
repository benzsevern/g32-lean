import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0306

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_078 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 78 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_078_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 0 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 0 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 13 14, g32p_row02_traceSegment_078_0000_0013, g32p_row02_traceSegment_078_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 27 13 14, g32p_row02_traceSegment_078_0027_0013, g32p_row02_traceSegment_078_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 0 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 27 27, g32p_row02_traceSegment_078_0000_0027, g32p_row02_traceSegment_078_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 54 13 14, g32p_row02_traceSegment_078_0054_0013, g32p_row02_traceSegment_078_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 81 13 14, g32p_row02_traceSegment_078_0081_0013, g32p_row02_traceSegment_078_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 54 27 27, g32p_row02_traceSegment_078_0054_0027, g32p_row02_traceSegment_078_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 0 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 54 54, g32p_row02_traceSegment_078_0000_0054, g32p_row02_traceSegment_078_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 108 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 108 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 108 13 14, g32p_row02_traceSegment_078_0108_0013, g32p_row02_traceSegment_078_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 135 13 14, g32p_row02_traceSegment_078_0135_0013, g32p_row02_traceSegment_078_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 108 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 108 27 27, g32p_row02_traceSegment_078_0108_0027, g32p_row02_traceSegment_078_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 162 13 14, g32p_row02_traceSegment_078_0162_0013, g32p_row02_traceSegment_078_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 189 13 14, g32p_row02_traceSegment_078_0189_0013, g32p_row02_traceSegment_078_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 162 27 27, g32p_row02_traceSegment_078_0162_0027, g32p_row02_traceSegment_078_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 108 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 108 54 54, g32p_row02_traceSegment_078_0108_0054, g32p_row02_traceSegment_078_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 0 216 = [0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 108 108, g32p_row02_traceSegment_078_0000_0108, g32p_row02_traceSegment_078_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 216 13 14, g32p_row02_traceSegment_078_0216_0013, g32p_row02_traceSegment_078_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 243 13 14, g32p_row02_traceSegment_078_0243_0013, g32p_row02_traceSegment_078_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 216 27 27, g32p_row02_traceSegment_078_0216_0027, g32p_row02_traceSegment_078_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 270 13 14, g32p_row02_traceSegment_078_0270_0013, g32p_row02_traceSegment_078_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 297 13 14, g32p_row02_traceSegment_078_0297_0013, g32p_row02_traceSegment_078_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 270 27 27, g32p_row02_traceSegment_078_0270_0027, g32p_row02_traceSegment_078_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 216 54 54, g32p_row02_traceSegment_078_0216_0054, g32p_row02_traceSegment_078_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 324 13 14, g32p_row02_traceSegment_078_0324_0013, g32p_row02_traceSegment_078_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 351 13 14, g32p_row02_traceSegment_078_0351_0013, g32p_row02_traceSegment_078_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 324 27 27, g32p_row02_traceSegment_078_0324_0027, g32p_row02_traceSegment_078_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 378 13 14, g32p_row02_traceSegment_078_0378_0013, g32p_row02_traceSegment_078_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 405 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 405 13 14, g32p_row02_traceSegment_078_0405_0013, g32p_row02_traceSegment_078_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 378 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 378 27 27, g32p_row02_traceSegment_078_0378_0027, g32p_row02_traceSegment_078_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 324 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 324 54 54, g32p_row02_traceSegment_078_0324_0054, g32p_row02_traceSegment_078_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 216 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 216 108 108, g32p_row02_traceSegment_078_0216_0108, g32p_row02_traceSegment_078_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 0 432 = [0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 216 216, g32p_row02_traceSegment_078_0000_0216, g32p_row02_traceSegment_078_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 432 13 14, g32p_row02_traceSegment_078_0432_0013, g32p_row02_traceSegment_078_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 472 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 459 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 459 13 14, g32p_row02_traceSegment_078_0459_0013, g32p_row02_traceSegment_078_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 432 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 432 27 27, g32p_row02_traceSegment_078_0432_0027, g32p_row02_traceSegment_078_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 486 13 14, g32p_row02_traceSegment_078_0486_0013, g32p_row02_traceSegment_078_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 513 13 14, g32p_row02_traceSegment_078_0513_0013, g32p_row02_traceSegment_078_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 486 27 27, g32p_row02_traceSegment_078_0486_0027, g32p_row02_traceSegment_078_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 432 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 432 54 54, g32p_row02_traceSegment_078_0432_0054, g32p_row02_traceSegment_078_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 540 13 14, g32p_row02_traceSegment_078_0540_0013, g32p_row02_traceSegment_078_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 580 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 567 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 567 13 14, g32p_row02_traceSegment_078_0567_0013, g32p_row02_traceSegment_078_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 540 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 540 27 27, g32p_row02_traceSegment_078_0540_0027, g32p_row02_traceSegment_078_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 594 13 14, g32p_row02_traceSegment_078_0594_0013, g32p_row02_traceSegment_078_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 621 13 14, g32p_row02_traceSegment_078_0621_0013, g32p_row02_traceSegment_078_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 594 27 27, g32p_row02_traceSegment_078_0594_0027, g32p_row02_traceSegment_078_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 540 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 540 54 54, g32p_row02_traceSegment_078_0540_0054, g32p_row02_traceSegment_078_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 432 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 432 108 108, g32p_row02_traceSegment_078_0432_0108, g32p_row02_traceSegment_078_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 648 13 14, g32p_row02_traceSegment_078_0648_0013, g32p_row02_traceSegment_078_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 675 13 14, g32p_row02_traceSegment_078_0675_0013, g32p_row02_traceSegment_078_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 648 27 27, g32p_row02_traceSegment_078_0648_0027, g32p_row02_traceSegment_078_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 702 13 14, g32p_row02_traceSegment_078_0702_0013, g32p_row02_traceSegment_078_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 729 13 14, g32p_row02_traceSegment_078_0729_0013, g32p_row02_traceSegment_078_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 702 27 27, g32p_row02_traceSegment_078_0702_0027, g32p_row02_traceSegment_078_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 648 54 54, g32p_row02_traceSegment_078_0648_0054, g32p_row02_traceSegment_078_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 756 13 14, g32p_row02_traceSegment_078_0756_0013, g32p_row02_traceSegment_078_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 783 13 14, g32p_row02_traceSegment_078_0783_0013, g32p_row02_traceSegment_078_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 756 27 27, g32p_row02_traceSegment_078_0756_0027, g32p_row02_traceSegment_078_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 810 13 14, g32p_row02_traceSegment_078_0810_0013, g32p_row02_traceSegment_078_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 837 13 14, g32p_row02_traceSegment_078_0837_0013, g32p_row02_traceSegment_078_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 810 27 27, g32p_row02_traceSegment_078_0810_0027, g32p_row02_traceSegment_078_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 756 54 54, g32p_row02_traceSegment_078_0756_0054, g32p_row02_traceSegment_078_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 648 108 108, g32p_row02_traceSegment_078_0648_0108, g32p_row02_traceSegment_078_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 432 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 432 216 216, g32p_row02_traceSegment_078_0432_0216, g32p_row02_traceSegment_078_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_078 0 864 = [0, 0, 2, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 432 432, g32p_row02_traceSegment_078_0000_0432, g32p_row02_traceSegment_078_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 864 13 14, g32p_row02_traceSegment_078_0864_0013, g32p_row02_traceSegment_078_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 891 13 14, g32p_row02_traceSegment_078_0891_0013, g32p_row02_traceSegment_078_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 864 27 27, g32p_row02_traceSegment_078_0864_0027, g32p_row02_traceSegment_078_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 918 13 14, g32p_row02_traceSegment_078_0918_0013, g32p_row02_traceSegment_078_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 958 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 945 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 945 13 14, g32p_row02_traceSegment_078_0945_0013, g32p_row02_traceSegment_078_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 918 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 918 27 27, g32p_row02_traceSegment_078_0918_0027, g32p_row02_traceSegment_078_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 864 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 864 54 54, g32p_row02_traceSegment_078_0864_0054, g32p_row02_traceSegment_078_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 972 13 14, g32p_row02_traceSegment_078_0972_0013, g32p_row02_traceSegment_078_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 999 13 14, g32p_row02_traceSegment_078_0999_0013, g32p_row02_traceSegment_078_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 972 27 27, g32p_row02_traceSegment_078_0972_0027, g32p_row02_traceSegment_078_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1026 13 14, g32p_row02_traceSegment_078_1026_0013, g32p_row02_traceSegment_078_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1053 13 14, g32p_row02_traceSegment_078_1053_0013, g32p_row02_traceSegment_078_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1026 27 27, g32p_row02_traceSegment_078_1026_0027, g32p_row02_traceSegment_078_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 972 54 54, g32p_row02_traceSegment_078_0972_0054, g32p_row02_traceSegment_078_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 864 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 864 108 108, g32p_row02_traceSegment_078_0864_0108, g32p_row02_traceSegment_078_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1080 13 14, g32p_row02_traceSegment_078_1080_0013, g32p_row02_traceSegment_078_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1107 13 14, g32p_row02_traceSegment_078_1107_0013, g32p_row02_traceSegment_078_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1080 27 27, g32p_row02_traceSegment_078_1080_0027, g32p_row02_traceSegment_078_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1134 13 14, g32p_row02_traceSegment_078_1134_0013, g32p_row02_traceSegment_078_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1161 13 14, g32p_row02_traceSegment_078_1161_0013, g32p_row02_traceSegment_078_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1134 27 27, g32p_row02_traceSegment_078_1134_0027, g32p_row02_traceSegment_078_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1080 54 54, g32p_row02_traceSegment_078_1080_0054, g32p_row02_traceSegment_078_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1201 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1188 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1188 13 14, g32p_row02_traceSegment_078_1188_0013, g32p_row02_traceSegment_078_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1215 13 14, g32p_row02_traceSegment_078_1215_0013, g32p_row02_traceSegment_078_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1188 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1188 27 27, g32p_row02_traceSegment_078_1188_0027, g32p_row02_traceSegment_078_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1242 13 14, g32p_row02_traceSegment_078_1242_0013, g32p_row02_traceSegment_078_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1269 13 14, g32p_row02_traceSegment_078_1269_0013, g32p_row02_traceSegment_078_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1242 27 27, g32p_row02_traceSegment_078_1242_0027, g32p_row02_traceSegment_078_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1188 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1188 54 54, g32p_row02_traceSegment_078_1188_0054, g32p_row02_traceSegment_078_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 1080 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1080 108 108, g32p_row02_traceSegment_078_1080_0108, g32p_row02_traceSegment_078_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 864 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 864 216 216, g32p_row02_traceSegment_078_0864_0216, g32p_row02_traceSegment_078_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1296 13 14, g32p_row02_traceSegment_078_1296_0013, g32p_row02_traceSegment_078_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1323 13 14, g32p_row02_traceSegment_078_1323_0013, g32p_row02_traceSegment_078_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1296 27 27, g32p_row02_traceSegment_078_1296_0027, g32p_row02_traceSegment_078_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1350 13 14, g32p_row02_traceSegment_078_1350_0013, g32p_row02_traceSegment_078_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1377 13 14, g32p_row02_traceSegment_078_1377_0013, g32p_row02_traceSegment_078_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1350 27 27, g32p_row02_traceSegment_078_1350_0027, g32p_row02_traceSegment_078_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1296 54 54, g32p_row02_traceSegment_078_1296_0054, g32p_row02_traceSegment_078_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1404 13 14, g32p_row02_traceSegment_078_1404_0013, g32p_row02_traceSegment_078_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1431 13 14, g32p_row02_traceSegment_078_1431_0013, g32p_row02_traceSegment_078_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1404 27 27, g32p_row02_traceSegment_078_1404_0027, g32p_row02_traceSegment_078_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1458 13 14, g32p_row02_traceSegment_078_1458_0013, g32p_row02_traceSegment_078_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1485 13 14, g32p_row02_traceSegment_078_1485_0013, g32p_row02_traceSegment_078_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1458 27 27, g32p_row02_traceSegment_078_1458_0027, g32p_row02_traceSegment_078_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1404 54 54, g32p_row02_traceSegment_078_1404_0054, g32p_row02_traceSegment_078_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1296 108 108, g32p_row02_traceSegment_078_1296_0108, g32p_row02_traceSegment_078_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1512 13 14, g32p_row02_traceSegment_078_1512_0013, g32p_row02_traceSegment_078_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1552 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1539 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1539 13 14, g32p_row02_traceSegment_078_1539_0013, g32p_row02_traceSegment_078_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1512 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1512 27 27, g32p_row02_traceSegment_078_1512_0027, g32p_row02_traceSegment_078_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1566 13 14, g32p_row02_traceSegment_078_1566_0013, g32p_row02_traceSegment_078_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1593 13 14, g32p_row02_traceSegment_078_1593_0013, g32p_row02_traceSegment_078_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1566 27 27, g32p_row02_traceSegment_078_1566_0027, g32p_row02_traceSegment_078_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1512 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1512 54 54, g32p_row02_traceSegment_078_1512_0054, g32p_row02_traceSegment_078_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1620 13 14, g32p_row02_traceSegment_078_1620_0013, g32p_row02_traceSegment_078_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1647 13 14, g32p_row02_traceSegment_078_1647_0013, g32p_row02_traceSegment_078_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1620 27 27, g32p_row02_traceSegment_078_1620_0027, g32p_row02_traceSegment_078_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1674 13 14, g32p_row02_traceSegment_078_1674_0013, g32p_row02_traceSegment_078_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1701 13 14, g32p_row02_traceSegment_078_1701_0013, g32p_row02_traceSegment_078_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1674 27 27, g32p_row02_traceSegment_078_1674_0027, g32p_row02_traceSegment_078_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1620 54 54, g32p_row02_traceSegment_078_1620_0054, g32p_row02_traceSegment_078_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 1512 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1512 108 108, g32p_row02_traceSegment_078_1512_0108, g32p_row02_traceSegment_078_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 1296 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1296 216 216, g32p_row02_traceSegment_078_1296_0216, g32p_row02_traceSegment_078_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_078 864 864 = [0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 864 432 432, g32p_row02_traceSegment_078_0864_0432, g32p_row02_traceSegment_078_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_078 0 1728 = [0, 0, 4, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 864 864, g32p_row02_traceSegment_078_0000_0864, g32p_row02_traceSegment_078_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1728 13 14, g32p_row02_traceSegment_078_1728_0013, g32p_row02_traceSegment_078_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1755 13 14, g32p_row02_traceSegment_078_1755_0013, g32p_row02_traceSegment_078_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1728 27 27, g32p_row02_traceSegment_078_1728_0027, g32p_row02_traceSegment_078_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1782 13 14, g32p_row02_traceSegment_078_1782_0013, g32p_row02_traceSegment_078_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1809 13 14, g32p_row02_traceSegment_078_1809_0013, g32p_row02_traceSegment_078_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1782 27 27, g32p_row02_traceSegment_078_1782_0027, g32p_row02_traceSegment_078_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1728 54 54, g32p_row02_traceSegment_078_1728_0054, g32p_row02_traceSegment_078_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1836 13 14, g32p_row02_traceSegment_078_1836_0013, g32p_row02_traceSegment_078_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1876 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1863 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1863 13 14, g32p_row02_traceSegment_078_1863_0013, g32p_row02_traceSegment_078_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1836 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1836 27 27, g32p_row02_traceSegment_078_1836_0027, g32p_row02_traceSegment_078_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1890 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1890 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1890 13 14, g32p_row02_traceSegment_078_1890_0013, g32p_row02_traceSegment_078_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1917 13 14, g32p_row02_traceSegment_078_1917_0013, g32p_row02_traceSegment_078_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1890 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1890 27 27, g32p_row02_traceSegment_078_1890_0027, g32p_row02_traceSegment_078_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1836 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1836 54 54, g32p_row02_traceSegment_078_1836_0054, g32p_row02_traceSegment_078_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1728 108 108, g32p_row02_traceSegment_078_1728_0108, g32p_row02_traceSegment_078_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1944 13 14, g32p_row02_traceSegment_078_1944_0013, g32p_row02_traceSegment_078_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1971 13 14, g32p_row02_traceSegment_078_1971_0013, g32p_row02_traceSegment_078_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1944 27 27, g32p_row02_traceSegment_078_1944_0027, g32p_row02_traceSegment_078_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1998 13 14, g32p_row02_traceSegment_078_1998_0013, g32p_row02_traceSegment_078_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2025 13 14, g32p_row02_traceSegment_078_2025_0013, g32p_row02_traceSegment_078_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1998 27 27, g32p_row02_traceSegment_078_1998_0027, g32p_row02_traceSegment_078_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1944 54 54, g32p_row02_traceSegment_078_1944_0054, g32p_row02_traceSegment_078_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2052 13 14, g32p_row02_traceSegment_078_2052_0013, g32p_row02_traceSegment_078_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2079 13 14, g32p_row02_traceSegment_078_2079_0013, g32p_row02_traceSegment_078_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2052 27 27, g32p_row02_traceSegment_078_2052_0027, g32p_row02_traceSegment_078_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2106 13 14, g32p_row02_traceSegment_078_2106_0013, g32p_row02_traceSegment_078_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2133 13 14, g32p_row02_traceSegment_078_2133_0013, g32p_row02_traceSegment_078_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2106 27 27, g32p_row02_traceSegment_078_2106_0027, g32p_row02_traceSegment_078_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2052 54 54, g32p_row02_traceSegment_078_2052_0054, g32p_row02_traceSegment_078_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1944 108 108, g32p_row02_traceSegment_078_1944_0108, g32p_row02_traceSegment_078_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1728 216 216, g32p_row02_traceSegment_078_1728_0216, g32p_row02_traceSegment_078_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2160 13 14, g32p_row02_traceSegment_078_2160_0013, g32p_row02_traceSegment_078_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2200 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2187 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2187 13 14, g32p_row02_traceSegment_078_2187_0013, g32p_row02_traceSegment_078_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2160 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2160 27 27, g32p_row02_traceSegment_078_2160_0027, g32p_row02_traceSegment_078_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2214 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2214 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2214 13 14, g32p_row02_traceSegment_078_2214_0013, g32p_row02_traceSegment_078_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2241 13 14, g32p_row02_traceSegment_078_2241_0013, g32p_row02_traceSegment_078_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2214 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2214 27 27, g32p_row02_traceSegment_078_2214_0027, g32p_row02_traceSegment_078_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2160 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2160 54 54, g32p_row02_traceSegment_078_2160_0054, g32p_row02_traceSegment_078_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2268 13 14, g32p_row02_traceSegment_078_2268_0013, g32p_row02_traceSegment_078_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2308 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2295 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2295 13 14, g32p_row02_traceSegment_078_2295_0013, g32p_row02_traceSegment_078_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2268 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2268 27 27, g32p_row02_traceSegment_078_2268_0027, g32p_row02_traceSegment_078_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2322 13 14, g32p_row02_traceSegment_078_2322_0013, g32p_row02_traceSegment_078_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2349 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2362 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2349 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2349 13 14, g32p_row02_traceSegment_078_2349_0013, g32p_row02_traceSegment_078_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2322 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2322 27 27, g32p_row02_traceSegment_078_2322_0027, g32p_row02_traceSegment_078_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2268 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2268 54 54, g32p_row02_traceSegment_078_2268_0054, g32p_row02_traceSegment_078_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 2160 216 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2160 108 108, g32p_row02_traceSegment_078_2160_0108, g32p_row02_traceSegment_078_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2376 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2389 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2376 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2376 13 14, g32p_row02_traceSegment_078_2376_0013, g32p_row02_traceSegment_078_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2403 13 14, g32p_row02_traceSegment_078_2403_0013, g32p_row02_traceSegment_078_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2376 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2376 27 27, g32p_row02_traceSegment_078_2376_0027, g32p_row02_traceSegment_078_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2430 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2443 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2430 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2430 13 14, g32p_row02_traceSegment_078_2430_0013, g32p_row02_traceSegment_078_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2457 13 14, g32p_row02_traceSegment_078_2457_0013, g32p_row02_traceSegment_078_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2430 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2430 27 27, g32p_row02_traceSegment_078_2430_0027, g32p_row02_traceSegment_078_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2376 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2376 54 54, g32p_row02_traceSegment_078_2376_0054, g32p_row02_traceSegment_078_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2497 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2484 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2484 13 14, g32p_row02_traceSegment_078_2484_0013, g32p_row02_traceSegment_078_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2511 13 14, g32p_row02_traceSegment_078_2511_0013, g32p_row02_traceSegment_078_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2484 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2484 27 27, g32p_row02_traceSegment_078_2484_0027, g32p_row02_traceSegment_078_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2538 13 14, g32p_row02_traceSegment_078_2538_0013, g32p_row02_traceSegment_078_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2565 13 14, g32p_row02_traceSegment_078_2565_0013, g32p_row02_traceSegment_078_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2538 27 27, g32p_row02_traceSegment_078_2538_0027, g32p_row02_traceSegment_078_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2484 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2484 54 54, g32p_row02_traceSegment_078_2484_0054, g32p_row02_traceSegment_078_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 2376 216 = [0, 0, 2, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2376 108 108, g32p_row02_traceSegment_078_2376_0108, g32p_row02_traceSegment_078_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 2160 432 = [0, 0, 2, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2160 216 216, g32p_row02_traceSegment_078_2160_0216, g32p_row02_traceSegment_078_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 864 = [0, 0, 2, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1728 432 432, g32p_row02_traceSegment_078_1728_0432, g32p_row02_traceSegment_078_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2592 13 14, g32p_row02_traceSegment_078_2592_0013, g32p_row02_traceSegment_078_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2619 13 14, g32p_row02_traceSegment_078_2619_0013, g32p_row02_traceSegment_078_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2592 27 27, g32p_row02_traceSegment_078_2592_0027, g32p_row02_traceSegment_078_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2646 13 14, g32p_row02_traceSegment_078_2646_0013, g32p_row02_traceSegment_078_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2673 13 14, g32p_row02_traceSegment_078_2673_0013, g32p_row02_traceSegment_078_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2646 27 27, g32p_row02_traceSegment_078_2646_0027, g32p_row02_traceSegment_078_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2592 54 54, g32p_row02_traceSegment_078_2592_0054, g32p_row02_traceSegment_078_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2700 13 14, g32p_row02_traceSegment_078_2700_0013, g32p_row02_traceSegment_078_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2727 13 14, g32p_row02_traceSegment_078_2727_0013, g32p_row02_traceSegment_078_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2700 27 27, g32p_row02_traceSegment_078_2700_0027, g32p_row02_traceSegment_078_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2754 13 14, g32p_row02_traceSegment_078_2754_0013, g32p_row02_traceSegment_078_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2781 13 14, g32p_row02_traceSegment_078_2781_0013, g32p_row02_traceSegment_078_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2754 27 27, g32p_row02_traceSegment_078_2754_0027, g32p_row02_traceSegment_078_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2700 54 54, g32p_row02_traceSegment_078_2700_0054, g32p_row02_traceSegment_078_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2592 108 108, g32p_row02_traceSegment_078_2592_0108, g32p_row02_traceSegment_078_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2808 13 14, g32p_row02_traceSegment_078_2808_0013, g32p_row02_traceSegment_078_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2835 13 14, g32p_row02_traceSegment_078_2835_0013, g32p_row02_traceSegment_078_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2808 27 27, g32p_row02_traceSegment_078_2808_0027, g32p_row02_traceSegment_078_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2862 13 14, g32p_row02_traceSegment_078_2862_0013, g32p_row02_traceSegment_078_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2889 13 14, g32p_row02_traceSegment_078_2889_0013, g32p_row02_traceSegment_078_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2862 27 27, g32p_row02_traceSegment_078_2862_0027, g32p_row02_traceSegment_078_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2808 54 54, g32p_row02_traceSegment_078_2808_0054, g32p_row02_traceSegment_078_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2916 13 14, g32p_row02_traceSegment_078_2916_0013, g32p_row02_traceSegment_078_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2943 13 14, g32p_row02_traceSegment_078_2943_0013, g32p_row02_traceSegment_078_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2916 27 27, g32p_row02_traceSegment_078_2916_0027, g32p_row02_traceSegment_078_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2970 13 14, g32p_row02_traceSegment_078_2970_0013, g32p_row02_traceSegment_078_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2997 13 14, g32p_row02_traceSegment_078_2997_0013, g32p_row02_traceSegment_078_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2970 27 27, g32p_row02_traceSegment_078_2970_0027, g32p_row02_traceSegment_078_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2916 54 54, g32p_row02_traceSegment_078_2916_0054, g32p_row02_traceSegment_078_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2808 108 108, g32p_row02_traceSegment_078_2808_0108, g32p_row02_traceSegment_078_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2592 216 216, g32p_row02_traceSegment_078_2592_0216, g32p_row02_traceSegment_078_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3024 13 14, g32p_row02_traceSegment_078_3024_0013, g32p_row02_traceSegment_078_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3051 13 14, g32p_row02_traceSegment_078_3051_0013, g32p_row02_traceSegment_078_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3024 27 27, g32p_row02_traceSegment_078_3024_0027, g32p_row02_traceSegment_078_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3078 13 14, g32p_row02_traceSegment_078_3078_0013, g32p_row02_traceSegment_078_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3105 13 14, g32p_row02_traceSegment_078_3105_0013, g32p_row02_traceSegment_078_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3078 27 27, g32p_row02_traceSegment_078_3078_0027, g32p_row02_traceSegment_078_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3024 54 54, g32p_row02_traceSegment_078_3024_0054, g32p_row02_traceSegment_078_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3132 13 14, g32p_row02_traceSegment_078_3132_0013, g32p_row02_traceSegment_078_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3159 13 14, g32p_row02_traceSegment_078_3159_0013, g32p_row02_traceSegment_078_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3132 27 27, g32p_row02_traceSegment_078_3132_0027, g32p_row02_traceSegment_078_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3186 13 14, g32p_row02_traceSegment_078_3186_0013, g32p_row02_traceSegment_078_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3213 13 14, g32p_row02_traceSegment_078_3213_0013, g32p_row02_traceSegment_078_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3186 27 27, g32p_row02_traceSegment_078_3186_0027, g32p_row02_traceSegment_078_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3132 54 54, g32p_row02_traceSegment_078_3132_0054, g32p_row02_traceSegment_078_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3024 108 108, g32p_row02_traceSegment_078_3024_0108, g32p_row02_traceSegment_078_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3240 13 14, g32p_row02_traceSegment_078_3240_0013, g32p_row02_traceSegment_078_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3267 13 14, g32p_row02_traceSegment_078_3267_0013, g32p_row02_traceSegment_078_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3240 27 27, g32p_row02_traceSegment_078_3240_0027, g32p_row02_traceSegment_078_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3294 13 14, g32p_row02_traceSegment_078_3294_0013, g32p_row02_traceSegment_078_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3321 13 14, g32p_row02_traceSegment_078_3321_0013, g32p_row02_traceSegment_078_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3294 27 27, g32p_row02_traceSegment_078_3294_0027, g32p_row02_traceSegment_078_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3240 54 54, g32p_row02_traceSegment_078_3240_0054, g32p_row02_traceSegment_078_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3348 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3361 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3348 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3348 13 14, g32p_row02_traceSegment_078_3348_0013, g32p_row02_traceSegment_078_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3375 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3388 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3375 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3375 13 14, g32p_row02_traceSegment_078_3375_0013, g32p_row02_traceSegment_078_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3348 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3348 27 27, g32p_row02_traceSegment_078_3348_0027, g32p_row02_traceSegment_078_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3402 13 14, g32p_row02_traceSegment_078_3402_0013, g32p_row02_traceSegment_078_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_078 3429 13 = [0, 0, 5] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_078 3442 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_078_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_078 3429 27 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3429 13 14, g32p_row02_traceSegment_078_3429_0013, g32p_row02_traceSegment_078_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_078 3402 54 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3402 27 27, g32p_row02_traceSegment_078_3402_0027, g32p_row02_traceSegment_078_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_078 3348 108 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3348 54 54, g32p_row02_traceSegment_078_3348_0054, g32p_row02_traceSegment_078_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_078 3240 216 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3240 108 108, g32p_row02_traceSegment_078_3240_0108, g32p_row02_traceSegment_078_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_078_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_078 3024 432 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 3024 216 216, g32p_row02_traceSegment_078_3024_0216, g32p_row02_traceSegment_078_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_078_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_078 2592 864 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 2592 432 432, g32p_row02_traceSegment_078_2592_0432, g32p_row02_traceSegment_078_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_078_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_078 1728 1728 = [0, 0, 12, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 1728 864 864, g32p_row02_traceSegment_078_1728_0864, g32p_row02_traceSegment_078_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_078_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_078 0 3456 = [0, 0, 16, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_078 0 1728 1728, g32p_row02_traceSegment_078_0000_1728, g32p_row02_traceSegment_078_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_078 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 78 = [0, 0, 16, 0, 16] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_078_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_079 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 79 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_079_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 13 14, g32p_row02_traceSegment_079_0000_0013, g32p_row02_traceSegment_079_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 27 13 14, g32p_row02_traceSegment_079_0027_0013, g32p_row02_traceSegment_079_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 27 27, g32p_row02_traceSegment_079_0000_0027, g32p_row02_traceSegment_079_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 54 13 14, g32p_row02_traceSegment_079_0054_0013, g32p_row02_traceSegment_079_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 81 13 14, g32p_row02_traceSegment_079_0081_0013, g32p_row02_traceSegment_079_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 54 27 27, g32p_row02_traceSegment_079_0054_0027, g32p_row02_traceSegment_079_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 54 54, g32p_row02_traceSegment_079_0000_0054, g32p_row02_traceSegment_079_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 108 13 14, g32p_row02_traceSegment_079_0108_0013, g32p_row02_traceSegment_079_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 135 13 14, g32p_row02_traceSegment_079_0135_0013, g32p_row02_traceSegment_079_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 108 27 27, g32p_row02_traceSegment_079_0108_0027, g32p_row02_traceSegment_079_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 162 13 14, g32p_row02_traceSegment_079_0162_0013, g32p_row02_traceSegment_079_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 189 13 14, g32p_row02_traceSegment_079_0189_0013, g32p_row02_traceSegment_079_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 162 27 27, g32p_row02_traceSegment_079_0162_0027, g32p_row02_traceSegment_079_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 108 54 54, g32p_row02_traceSegment_079_0108_0054, g32p_row02_traceSegment_079_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 108 108, g32p_row02_traceSegment_079_0000_0108, g32p_row02_traceSegment_079_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 216 13 14, g32p_row02_traceSegment_079_0216_0013, g32p_row02_traceSegment_079_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 243 13 14, g32p_row02_traceSegment_079_0243_0013, g32p_row02_traceSegment_079_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 216 27 27, g32p_row02_traceSegment_079_0216_0027, g32p_row02_traceSegment_079_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 270 13 14, g32p_row02_traceSegment_079_0270_0013, g32p_row02_traceSegment_079_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 297 13 14, g32p_row02_traceSegment_079_0297_0013, g32p_row02_traceSegment_079_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 270 27 27, g32p_row02_traceSegment_079_0270_0027, g32p_row02_traceSegment_079_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 216 54 54, g32p_row02_traceSegment_079_0216_0054, g32p_row02_traceSegment_079_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 324 13 14, g32p_row02_traceSegment_079_0324_0013, g32p_row02_traceSegment_079_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 351 13 14, g32p_row02_traceSegment_079_0351_0013, g32p_row02_traceSegment_079_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 324 27 27, g32p_row02_traceSegment_079_0324_0027, g32p_row02_traceSegment_079_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 378 13 14, g32p_row02_traceSegment_079_0378_0013, g32p_row02_traceSegment_079_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 405 13 14, g32p_row02_traceSegment_079_0405_0013, g32p_row02_traceSegment_079_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 378 27 27, g32p_row02_traceSegment_079_0378_0027, g32p_row02_traceSegment_079_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 324 54 54, g32p_row02_traceSegment_079_0324_0054, g32p_row02_traceSegment_079_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 216 108 108, g32p_row02_traceSegment_079_0216_0108, g32p_row02_traceSegment_079_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 216 216, g32p_row02_traceSegment_079_0000_0216, g32p_row02_traceSegment_079_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 432 13 14, g32p_row02_traceSegment_079_0432_0013, g32p_row02_traceSegment_079_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 459 13 14, g32p_row02_traceSegment_079_0459_0013, g32p_row02_traceSegment_079_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 432 27 27, g32p_row02_traceSegment_079_0432_0027, g32p_row02_traceSegment_079_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 486 13 14, g32p_row02_traceSegment_079_0486_0013, g32p_row02_traceSegment_079_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 513 13 14, g32p_row02_traceSegment_079_0513_0013, g32p_row02_traceSegment_079_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 486 27 27, g32p_row02_traceSegment_079_0486_0027, g32p_row02_traceSegment_079_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 432 54 54, g32p_row02_traceSegment_079_0432_0054, g32p_row02_traceSegment_079_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 540 13 14, g32p_row02_traceSegment_079_0540_0013, g32p_row02_traceSegment_079_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 567 13 14, g32p_row02_traceSegment_079_0567_0013, g32p_row02_traceSegment_079_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 540 27 27, g32p_row02_traceSegment_079_0540_0027, g32p_row02_traceSegment_079_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 594 13 14, g32p_row02_traceSegment_079_0594_0013, g32p_row02_traceSegment_079_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 621 13 14, g32p_row02_traceSegment_079_0621_0013, g32p_row02_traceSegment_079_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 594 27 27, g32p_row02_traceSegment_079_0594_0027, g32p_row02_traceSegment_079_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 540 54 54, g32p_row02_traceSegment_079_0540_0054, g32p_row02_traceSegment_079_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 432 108 108, g32p_row02_traceSegment_079_0432_0108, g32p_row02_traceSegment_079_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 648 13 14, g32p_row02_traceSegment_079_0648_0013, g32p_row02_traceSegment_079_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 675 13 14, g32p_row02_traceSegment_079_0675_0013, g32p_row02_traceSegment_079_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 648 27 27, g32p_row02_traceSegment_079_0648_0027, g32p_row02_traceSegment_079_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 702 13 14, g32p_row02_traceSegment_079_0702_0013, g32p_row02_traceSegment_079_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 729 13 14, g32p_row02_traceSegment_079_0729_0013, g32p_row02_traceSegment_079_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 702 27 27, g32p_row02_traceSegment_079_0702_0027, g32p_row02_traceSegment_079_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 648 54 54, g32p_row02_traceSegment_079_0648_0054, g32p_row02_traceSegment_079_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 756 13 14, g32p_row02_traceSegment_079_0756_0013, g32p_row02_traceSegment_079_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 783 13 14, g32p_row02_traceSegment_079_0783_0013, g32p_row02_traceSegment_079_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 756 27 27, g32p_row02_traceSegment_079_0756_0027, g32p_row02_traceSegment_079_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 810 13 14, g32p_row02_traceSegment_079_0810_0013, g32p_row02_traceSegment_079_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 837 13 14, g32p_row02_traceSegment_079_0837_0013, g32p_row02_traceSegment_079_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 810 27 27, g32p_row02_traceSegment_079_0810_0027, g32p_row02_traceSegment_079_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 756 54 54, g32p_row02_traceSegment_079_0756_0054, g32p_row02_traceSegment_079_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 648 108 108, g32p_row02_traceSegment_079_0648_0108, g32p_row02_traceSegment_079_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 432 216 216, g32p_row02_traceSegment_079_0432_0216, g32p_row02_traceSegment_079_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_079 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 432 432, g32p_row02_traceSegment_079_0000_0432, g32p_row02_traceSegment_079_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 864 13 14, g32p_row02_traceSegment_079_0864_0013, g32p_row02_traceSegment_079_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 891 13 14, g32p_row02_traceSegment_079_0891_0013, g32p_row02_traceSegment_079_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 864 27 27, g32p_row02_traceSegment_079_0864_0027, g32p_row02_traceSegment_079_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 918 13 14, g32p_row02_traceSegment_079_0918_0013, g32p_row02_traceSegment_079_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 945 13 14, g32p_row02_traceSegment_079_0945_0013, g32p_row02_traceSegment_079_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 918 27 27, g32p_row02_traceSegment_079_0918_0027, g32p_row02_traceSegment_079_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 864 54 54, g32p_row02_traceSegment_079_0864_0054, g32p_row02_traceSegment_079_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 972 13 14, g32p_row02_traceSegment_079_0972_0013, g32p_row02_traceSegment_079_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 999 13 14, g32p_row02_traceSegment_079_0999_0013, g32p_row02_traceSegment_079_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 972 27 27, g32p_row02_traceSegment_079_0972_0027, g32p_row02_traceSegment_079_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1026 13 14, g32p_row02_traceSegment_079_1026_0013, g32p_row02_traceSegment_079_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1053 13 14, g32p_row02_traceSegment_079_1053_0013, g32p_row02_traceSegment_079_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1026 27 27, g32p_row02_traceSegment_079_1026_0027, g32p_row02_traceSegment_079_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 972 54 54, g32p_row02_traceSegment_079_0972_0054, g32p_row02_traceSegment_079_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 864 108 108, g32p_row02_traceSegment_079_0864_0108, g32p_row02_traceSegment_079_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1080 13 14, g32p_row02_traceSegment_079_1080_0013, g32p_row02_traceSegment_079_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1107 13 14, g32p_row02_traceSegment_079_1107_0013, g32p_row02_traceSegment_079_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1080 27 27, g32p_row02_traceSegment_079_1080_0027, g32p_row02_traceSegment_079_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1134 13 14, g32p_row02_traceSegment_079_1134_0013, g32p_row02_traceSegment_079_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1161 13 14, g32p_row02_traceSegment_079_1161_0013, g32p_row02_traceSegment_079_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1134 27 27, g32p_row02_traceSegment_079_1134_0027, g32p_row02_traceSegment_079_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1080 54 54, g32p_row02_traceSegment_079_1080_0054, g32p_row02_traceSegment_079_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1188 13 14, g32p_row02_traceSegment_079_1188_0013, g32p_row02_traceSegment_079_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1215 13 14, g32p_row02_traceSegment_079_1215_0013, g32p_row02_traceSegment_079_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1188 27 27, g32p_row02_traceSegment_079_1188_0027, g32p_row02_traceSegment_079_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1242 13 14, g32p_row02_traceSegment_079_1242_0013, g32p_row02_traceSegment_079_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1269 13 14, g32p_row02_traceSegment_079_1269_0013, g32p_row02_traceSegment_079_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1242 27 27, g32p_row02_traceSegment_079_1242_0027, g32p_row02_traceSegment_079_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1188 54 54, g32p_row02_traceSegment_079_1188_0054, g32p_row02_traceSegment_079_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1080 108 108, g32p_row02_traceSegment_079_1080_0108, g32p_row02_traceSegment_079_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 864 216 216, g32p_row02_traceSegment_079_0864_0216, g32p_row02_traceSegment_079_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1296 13 14, g32p_row02_traceSegment_079_1296_0013, g32p_row02_traceSegment_079_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1323 13 14, g32p_row02_traceSegment_079_1323_0013, g32p_row02_traceSegment_079_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1296 27 27, g32p_row02_traceSegment_079_1296_0027, g32p_row02_traceSegment_079_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1350 13 14, g32p_row02_traceSegment_079_1350_0013, g32p_row02_traceSegment_079_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1377 13 14, g32p_row02_traceSegment_079_1377_0013, g32p_row02_traceSegment_079_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1350 27 27, g32p_row02_traceSegment_079_1350_0027, g32p_row02_traceSegment_079_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1296 54 54, g32p_row02_traceSegment_079_1296_0054, g32p_row02_traceSegment_079_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1404 13 14, g32p_row02_traceSegment_079_1404_0013, g32p_row02_traceSegment_079_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1431 13 14, g32p_row02_traceSegment_079_1431_0013, g32p_row02_traceSegment_079_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1404 27 27, g32p_row02_traceSegment_079_1404_0027, g32p_row02_traceSegment_079_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1458 13 14, g32p_row02_traceSegment_079_1458_0013, g32p_row02_traceSegment_079_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1485 13 14, g32p_row02_traceSegment_079_1485_0013, g32p_row02_traceSegment_079_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1458 27 27, g32p_row02_traceSegment_079_1458_0027, g32p_row02_traceSegment_079_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1404 54 54, g32p_row02_traceSegment_079_1404_0054, g32p_row02_traceSegment_079_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1296 108 108, g32p_row02_traceSegment_079_1296_0108, g32p_row02_traceSegment_079_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1512 13 14, g32p_row02_traceSegment_079_1512_0013, g32p_row02_traceSegment_079_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1539 13 14, g32p_row02_traceSegment_079_1539_0013, g32p_row02_traceSegment_079_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1512 27 27, g32p_row02_traceSegment_079_1512_0027, g32p_row02_traceSegment_079_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1566 13 14, g32p_row02_traceSegment_079_1566_0013, g32p_row02_traceSegment_079_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1593 13 14, g32p_row02_traceSegment_079_1593_0013, g32p_row02_traceSegment_079_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1566 27 27, g32p_row02_traceSegment_079_1566_0027, g32p_row02_traceSegment_079_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1512 54 54, g32p_row02_traceSegment_079_1512_0054, g32p_row02_traceSegment_079_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1620 13 14, g32p_row02_traceSegment_079_1620_0013, g32p_row02_traceSegment_079_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1647 13 14, g32p_row02_traceSegment_079_1647_0013, g32p_row02_traceSegment_079_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1620 27 27, g32p_row02_traceSegment_079_1620_0027, g32p_row02_traceSegment_079_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1674 13 14, g32p_row02_traceSegment_079_1674_0013, g32p_row02_traceSegment_079_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1701 13 14, g32p_row02_traceSegment_079_1701_0013, g32p_row02_traceSegment_079_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1674 27 27, g32p_row02_traceSegment_079_1674_0027, g32p_row02_traceSegment_079_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1620 54 54, g32p_row02_traceSegment_079_1620_0054, g32p_row02_traceSegment_079_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1512 108 108, g32p_row02_traceSegment_079_1512_0108, g32p_row02_traceSegment_079_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1296 216 216, g32p_row02_traceSegment_079_1296_0216, g32p_row02_traceSegment_079_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_079 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 864 432 432, g32p_row02_traceSegment_079_0864_0432, g32p_row02_traceSegment_079_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_079 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 864 864, g32p_row02_traceSegment_079_0000_0864, g32p_row02_traceSegment_079_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1728 13 14, g32p_row02_traceSegment_079_1728_0013, g32p_row02_traceSegment_079_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1755 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1768 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1755 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1755 13 14, g32p_row02_traceSegment_079_1755_0013, g32p_row02_traceSegment_079_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1728 27 27, g32p_row02_traceSegment_079_1728_0027, g32p_row02_traceSegment_079_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1782 13 14, g32p_row02_traceSegment_079_1782_0013, g32p_row02_traceSegment_079_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1809 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1809 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1809 13 14, g32p_row02_traceSegment_079_1809_0013, g32p_row02_traceSegment_079_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1782 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1782 27 27, g32p_row02_traceSegment_079_1782_0027, g32p_row02_traceSegment_079_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 108 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1728 54 54, g32p_row02_traceSegment_079_1728_0054, g32p_row02_traceSegment_079_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1836 13 14, g32p_row02_traceSegment_079_1836_0013, g32p_row02_traceSegment_079_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1863 13 14, g32p_row02_traceSegment_079_1863_0013, g32p_row02_traceSegment_079_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1836 27 27, g32p_row02_traceSegment_079_1836_0027, g32p_row02_traceSegment_079_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1890 13 14, g32p_row02_traceSegment_079_1890_0013, g32p_row02_traceSegment_079_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1917 13 14, g32p_row02_traceSegment_079_1917_0013, g32p_row02_traceSegment_079_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1890 27 27, g32p_row02_traceSegment_079_1890_0027, g32p_row02_traceSegment_079_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1836 54 54, g32p_row02_traceSegment_079_1836_0054, g32p_row02_traceSegment_079_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 216 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1728 108 108, g32p_row02_traceSegment_079_1728_0108, g32p_row02_traceSegment_079_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1944 13 14, g32p_row02_traceSegment_079_1944_0013, g32p_row02_traceSegment_079_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1971 13 14, g32p_row02_traceSegment_079_1971_0013, g32p_row02_traceSegment_079_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1944 27 27, g32p_row02_traceSegment_079_1944_0027, g32p_row02_traceSegment_079_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1998 13 14, g32p_row02_traceSegment_079_1998_0013, g32p_row02_traceSegment_079_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2025 13 14, g32p_row02_traceSegment_079_2025_0013, g32p_row02_traceSegment_079_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1998 27 27, g32p_row02_traceSegment_079_1998_0027, g32p_row02_traceSegment_079_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1944 54 54, g32p_row02_traceSegment_079_1944_0054, g32p_row02_traceSegment_079_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2052 13 14, g32p_row02_traceSegment_079_2052_0013, g32p_row02_traceSegment_079_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2079 13 14, g32p_row02_traceSegment_079_2079_0013, g32p_row02_traceSegment_079_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2052 27 27, g32p_row02_traceSegment_079_2052_0027, g32p_row02_traceSegment_079_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2106 13 14, g32p_row02_traceSegment_079_2106_0013, g32p_row02_traceSegment_079_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2133 13 14, g32p_row02_traceSegment_079_2133_0013, g32p_row02_traceSegment_079_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2106 27 27, g32p_row02_traceSegment_079_2106_0027, g32p_row02_traceSegment_079_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2052 54 54, g32p_row02_traceSegment_079_2052_0054, g32p_row02_traceSegment_079_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1944 108 108, g32p_row02_traceSegment_079_1944_0108, g32p_row02_traceSegment_079_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 432 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1728 216 216, g32p_row02_traceSegment_079_1728_0216, g32p_row02_traceSegment_079_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2173 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2160 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2160 13 14, g32p_row02_traceSegment_079_2160_0013, g32p_row02_traceSegment_079_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2187 13 14, g32p_row02_traceSegment_079_2187_0013, g32p_row02_traceSegment_079_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2160 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2160 27 27, g32p_row02_traceSegment_079_2160_0027, g32p_row02_traceSegment_079_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2214 13 14, g32p_row02_traceSegment_079_2214_0013, g32p_row02_traceSegment_079_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2241 13 14, g32p_row02_traceSegment_079_2241_0013, g32p_row02_traceSegment_079_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2214 27 27, g32p_row02_traceSegment_079_2214_0027, g32p_row02_traceSegment_079_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2160 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2160 54 54, g32p_row02_traceSegment_079_2160_0054, g32p_row02_traceSegment_079_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2268 13 14, g32p_row02_traceSegment_079_2268_0013, g32p_row02_traceSegment_079_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2295 13 14, g32p_row02_traceSegment_079_2295_0013, g32p_row02_traceSegment_079_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2268 27 27, g32p_row02_traceSegment_079_2268_0027, g32p_row02_traceSegment_079_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2322 13 14, g32p_row02_traceSegment_079_2322_0013, g32p_row02_traceSegment_079_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2349 13 14, g32p_row02_traceSegment_079_2349_0013, g32p_row02_traceSegment_079_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2322 27 27, g32p_row02_traceSegment_079_2322_0027, g32p_row02_traceSegment_079_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2268 54 54, g32p_row02_traceSegment_079_2268_0054, g32p_row02_traceSegment_079_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 2160 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2160 108 108, g32p_row02_traceSegment_079_2160_0108, g32p_row02_traceSegment_079_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2376 13 14, g32p_row02_traceSegment_079_2376_0013, g32p_row02_traceSegment_079_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2403 13 14, g32p_row02_traceSegment_079_2403_0013, g32p_row02_traceSegment_079_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2376 27 27, g32p_row02_traceSegment_079_2376_0027, g32p_row02_traceSegment_079_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2430 13 14, g32p_row02_traceSegment_079_2430_0013, g32p_row02_traceSegment_079_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2457 13 14, g32p_row02_traceSegment_079_2457_0013, g32p_row02_traceSegment_079_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2430 27 27, g32p_row02_traceSegment_079_2430_0027, g32p_row02_traceSegment_079_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2376 54 54, g32p_row02_traceSegment_079_2376_0054, g32p_row02_traceSegment_079_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2484 13 14, g32p_row02_traceSegment_079_2484_0013, g32p_row02_traceSegment_079_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2511 13 14, g32p_row02_traceSegment_079_2511_0013, g32p_row02_traceSegment_079_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2484 27 27, g32p_row02_traceSegment_079_2484_0027, g32p_row02_traceSegment_079_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2538 13 14, g32p_row02_traceSegment_079_2538_0013, g32p_row02_traceSegment_079_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2565 13 14, g32p_row02_traceSegment_079_2565_0013, g32p_row02_traceSegment_079_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2538 27 27, g32p_row02_traceSegment_079_2538_0027, g32p_row02_traceSegment_079_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2484 54 54, g32p_row02_traceSegment_079_2484_0054, g32p_row02_traceSegment_079_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2376 108 108, g32p_row02_traceSegment_079_2376_0108, g32p_row02_traceSegment_079_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 2160 432 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2160 216 216, g32p_row02_traceSegment_079_2160_0216, g32p_row02_traceSegment_079_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1728 432 432, g32p_row02_traceSegment_079_1728_0432, g32p_row02_traceSegment_079_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2592 13 14, g32p_row02_traceSegment_079_2592_0013, g32p_row02_traceSegment_079_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2619 13 14, g32p_row02_traceSegment_079_2619_0013, g32p_row02_traceSegment_079_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2592 27 27, g32p_row02_traceSegment_079_2592_0027, g32p_row02_traceSegment_079_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2646 13 14, g32p_row02_traceSegment_079_2646_0013, g32p_row02_traceSegment_079_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2673 13 14, g32p_row02_traceSegment_079_2673_0013, g32p_row02_traceSegment_079_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2646 27 27, g32p_row02_traceSegment_079_2646_0027, g32p_row02_traceSegment_079_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2592 54 54, g32p_row02_traceSegment_079_2592_0054, g32p_row02_traceSegment_079_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2700 13 14, g32p_row02_traceSegment_079_2700_0013, g32p_row02_traceSegment_079_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2727 13 14, g32p_row02_traceSegment_079_2727_0013, g32p_row02_traceSegment_079_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2700 27 27, g32p_row02_traceSegment_079_2700_0027, g32p_row02_traceSegment_079_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2754 13 14, g32p_row02_traceSegment_079_2754_0013, g32p_row02_traceSegment_079_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2781 13 14, g32p_row02_traceSegment_079_2781_0013, g32p_row02_traceSegment_079_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2754 27 27, g32p_row02_traceSegment_079_2754_0027, g32p_row02_traceSegment_079_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2700 54 54, g32p_row02_traceSegment_079_2700_0054, g32p_row02_traceSegment_079_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2592 108 108, g32p_row02_traceSegment_079_2592_0108, g32p_row02_traceSegment_079_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2808 13 14, g32p_row02_traceSegment_079_2808_0013, g32p_row02_traceSegment_079_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2835 13 14, g32p_row02_traceSegment_079_2835_0013, g32p_row02_traceSegment_079_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2808 27 27, g32p_row02_traceSegment_079_2808_0027, g32p_row02_traceSegment_079_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2862 13 14, g32p_row02_traceSegment_079_2862_0013, g32p_row02_traceSegment_079_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2889 13 14, g32p_row02_traceSegment_079_2889_0013, g32p_row02_traceSegment_079_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2862 27 27, g32p_row02_traceSegment_079_2862_0027, g32p_row02_traceSegment_079_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2808 54 54, g32p_row02_traceSegment_079_2808_0054, g32p_row02_traceSegment_079_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2916 13 14, g32p_row02_traceSegment_079_2916_0013, g32p_row02_traceSegment_079_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2943 13 14, g32p_row02_traceSegment_079_2943_0013, g32p_row02_traceSegment_079_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2916 27 27, g32p_row02_traceSegment_079_2916_0027, g32p_row02_traceSegment_079_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2970 13 14, g32p_row02_traceSegment_079_2970_0013, g32p_row02_traceSegment_079_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2997 13 14, g32p_row02_traceSegment_079_2997_0013, g32p_row02_traceSegment_079_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2970 27 27, g32p_row02_traceSegment_079_2970_0027, g32p_row02_traceSegment_079_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2916 54 54, g32p_row02_traceSegment_079_2916_0054, g32p_row02_traceSegment_079_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2808 108 108, g32p_row02_traceSegment_079_2808_0108, g32p_row02_traceSegment_079_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2592 216 216, g32p_row02_traceSegment_079_2592_0216, g32p_row02_traceSegment_079_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3024 13 14, g32p_row02_traceSegment_079_3024_0013, g32p_row02_traceSegment_079_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3051 13 14, g32p_row02_traceSegment_079_3051_0013, g32p_row02_traceSegment_079_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3024 27 27, g32p_row02_traceSegment_079_3024_0027, g32p_row02_traceSegment_079_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3078 13 14, g32p_row02_traceSegment_079_3078_0013, g32p_row02_traceSegment_079_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3105 13 14, g32p_row02_traceSegment_079_3105_0013, g32p_row02_traceSegment_079_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3078 27 27, g32p_row02_traceSegment_079_3078_0027, g32p_row02_traceSegment_079_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3024 54 54, g32p_row02_traceSegment_079_3024_0054, g32p_row02_traceSegment_079_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3132 13 14, g32p_row02_traceSegment_079_3132_0013, g32p_row02_traceSegment_079_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3159 13 14, g32p_row02_traceSegment_079_3159_0013, g32p_row02_traceSegment_079_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3132 27 27, g32p_row02_traceSegment_079_3132_0027, g32p_row02_traceSegment_079_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3186 13 14, g32p_row02_traceSegment_079_3186_0013, g32p_row02_traceSegment_079_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3213 13 14, g32p_row02_traceSegment_079_3213_0013, g32p_row02_traceSegment_079_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3186 27 27, g32p_row02_traceSegment_079_3186_0027, g32p_row02_traceSegment_079_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3132 54 54, g32p_row02_traceSegment_079_3132_0054, g32p_row02_traceSegment_079_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3024 108 108, g32p_row02_traceSegment_079_3024_0108, g32p_row02_traceSegment_079_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3253 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3240 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3240 13 14, g32p_row02_traceSegment_079_3240_0013, g32p_row02_traceSegment_079_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3267 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3280 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3267 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3267 13 14, g32p_row02_traceSegment_079_3267_0013, g32p_row02_traceSegment_079_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3240 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3240 27 27, g32p_row02_traceSegment_079_3240_0027, g32p_row02_traceSegment_079_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3294 13 14, g32p_row02_traceSegment_079_3294_0013, g32p_row02_traceSegment_079_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3321 13 14, g32p_row02_traceSegment_079_3321_0013, g32p_row02_traceSegment_079_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3294 27 27, g32p_row02_traceSegment_079_3294_0027, g32p_row02_traceSegment_079_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 3240 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3240 54 54, g32p_row02_traceSegment_079_3240_0054, g32p_row02_traceSegment_079_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3348 13 14, g32p_row02_traceSegment_079_3348_0013, g32p_row02_traceSegment_079_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3375 13 14, g32p_row02_traceSegment_079_3375_0013, g32p_row02_traceSegment_079_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3348 27 27, g32p_row02_traceSegment_079_3348_0027, g32p_row02_traceSegment_079_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3402 13 14, g32p_row02_traceSegment_079_3402_0013, g32p_row02_traceSegment_079_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_079 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_079 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_079_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_079 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3429 13 14, g32p_row02_traceSegment_079_3429_0013, g32p_row02_traceSegment_079_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_079 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3402 27 27, g32p_row02_traceSegment_079_3402_0027, g32p_row02_traceSegment_079_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_079 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3348 54 54, g32p_row02_traceSegment_079_3348_0054, g32p_row02_traceSegment_079_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_079 3240 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3240 108 108, g32p_row02_traceSegment_079_3240_0108, g32p_row02_traceSegment_079_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_079_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_079 3024 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 3024 216 216, g32p_row02_traceSegment_079_3024_0216, g32p_row02_traceSegment_079_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_079_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_079 2592 864 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 2592 432 432, g32p_row02_traceSegment_079_2592_0432, g32p_row02_traceSegment_079_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_079_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_079 1728 1728 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 1728 864 864, g32p_row02_traceSegment_079_1728_0864, g32p_row02_traceSegment_079_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_079_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_079 0 3456 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_079 0 1728 1728, g32p_row02_traceSegment_079_0000_1728, g32p_row02_traceSegment_079_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_079 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 79 = [0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_079_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_080 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 80 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_080_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 13 14, g32p_row02_traceSegment_080_0000_0013, g32p_row02_traceSegment_080_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 27 13 14, g32p_row02_traceSegment_080_0027_0013, g32p_row02_traceSegment_080_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 27 27, g32p_row02_traceSegment_080_0000_0027, g32p_row02_traceSegment_080_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 54 13 14, g32p_row02_traceSegment_080_0054_0013, g32p_row02_traceSegment_080_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 81 13 14, g32p_row02_traceSegment_080_0081_0013, g32p_row02_traceSegment_080_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 54 27 27, g32p_row02_traceSegment_080_0054_0027, g32p_row02_traceSegment_080_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 54 54, g32p_row02_traceSegment_080_0000_0054, g32p_row02_traceSegment_080_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 108 13 14, g32p_row02_traceSegment_080_0108_0013, g32p_row02_traceSegment_080_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 135 13 14, g32p_row02_traceSegment_080_0135_0013, g32p_row02_traceSegment_080_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 108 27 27, g32p_row02_traceSegment_080_0108_0027, g32p_row02_traceSegment_080_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 162 13 14, g32p_row02_traceSegment_080_0162_0013, g32p_row02_traceSegment_080_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 189 13 14, g32p_row02_traceSegment_080_0189_0013, g32p_row02_traceSegment_080_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 162 27 27, g32p_row02_traceSegment_080_0162_0027, g32p_row02_traceSegment_080_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 108 54 54, g32p_row02_traceSegment_080_0108_0054, g32p_row02_traceSegment_080_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 108 108, g32p_row02_traceSegment_080_0000_0108, g32p_row02_traceSegment_080_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 216 13 14, g32p_row02_traceSegment_080_0216_0013, g32p_row02_traceSegment_080_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 243 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 256 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 243 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 243 13 14, g32p_row02_traceSegment_080_0243_0013, g32p_row02_traceSegment_080_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 216 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 216 27 27, g32p_row02_traceSegment_080_0216_0027, g32p_row02_traceSegment_080_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 270 13 14, g32p_row02_traceSegment_080_0270_0013, g32p_row02_traceSegment_080_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 297 13 14, g32p_row02_traceSegment_080_0297_0013, g32p_row02_traceSegment_080_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 270 27 27, g32p_row02_traceSegment_080_0270_0027, g32p_row02_traceSegment_080_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 216 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 216 54 54, g32p_row02_traceSegment_080_0216_0054, g32p_row02_traceSegment_080_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 337 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 324 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 324 13 14, g32p_row02_traceSegment_080_0324_0013, g32p_row02_traceSegment_080_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 364 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 351 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 351 13 14, g32p_row02_traceSegment_080_0351_0013, g32p_row02_traceSegment_080_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 324 54 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 324 27 27, g32p_row02_traceSegment_080_0324_0027, g32p_row02_traceSegment_080_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 391 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 378 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 378 13 14, g32p_row02_traceSegment_080_0378_0013, g32p_row02_traceSegment_080_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 405 13 14, g32p_row02_traceSegment_080_0405_0013, g32p_row02_traceSegment_080_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 378 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 378 27 27, g32p_row02_traceSegment_080_0378_0027, g32p_row02_traceSegment_080_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 324 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 324 54 54, g32p_row02_traceSegment_080_0324_0054, g32p_row02_traceSegment_080_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 216 216 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 216 108 108, g32p_row02_traceSegment_080_0216_0108, g32p_row02_traceSegment_080_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 0 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 216 216, g32p_row02_traceSegment_080_0000_0216, g32p_row02_traceSegment_080_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 432 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 432 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 432 13 14, g32p_row02_traceSegment_080_0432_0013, g32p_row02_traceSegment_080_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 459 13 = [3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 472 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 459 27 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 459 13 14, g32p_row02_traceSegment_080_0459_0013, g32p_row02_traceSegment_080_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 432 54 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 432 27 27, g32p_row02_traceSegment_080_0432_0027, g32p_row02_traceSegment_080_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 486 13 14, g32p_row02_traceSegment_080_0486_0013, g32p_row02_traceSegment_080_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 526 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 513 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 513 13 14, g32p_row02_traceSegment_080_0513_0013, g32p_row02_traceSegment_080_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 486 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 486 27 27, g32p_row02_traceSegment_080_0486_0027, g32p_row02_traceSegment_080_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 432 108 = [7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 432 54 54, g32p_row02_traceSegment_080_0432_0054, g32p_row02_traceSegment_080_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 540 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 553 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 540 27 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 540 13 14, g32p_row02_traceSegment_080_0540_0013, g32p_row02_traceSegment_080_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 567 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 567 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 567 13 14, g32p_row02_traceSegment_080_0567_0013, g32p_row02_traceSegment_080_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 540 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 540 27 27, g32p_row02_traceSegment_080_0540_0027, g32p_row02_traceSegment_080_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 594 13 14, g32p_row02_traceSegment_080_0594_0013, g32p_row02_traceSegment_080_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 621 13 14, g32p_row02_traceSegment_080_0621_0013, g32p_row02_traceSegment_080_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 594 27 27, g32p_row02_traceSegment_080_0594_0027, g32p_row02_traceSegment_080_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 540 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 540 54 54, g32p_row02_traceSegment_080_0540_0054, g32p_row02_traceSegment_080_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 432 216 = [11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 432 108 108, g32p_row02_traceSegment_080_0432_0108, g32p_row02_traceSegment_080_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 648 13 14, g32p_row02_traceSegment_080_0648_0013, g32p_row02_traceSegment_080_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 675 13 14, g32p_row02_traceSegment_080_0675_0013, g32p_row02_traceSegment_080_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 648 27 27, g32p_row02_traceSegment_080_0648_0027, g32p_row02_traceSegment_080_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 702 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 702 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 702 13 14, g32p_row02_traceSegment_080_0702_0013, g32p_row02_traceSegment_080_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 729 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 729 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 729 13 14, g32p_row02_traceSegment_080_0729_0013, g32p_row02_traceSegment_080_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 702 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 702 27 27, g32p_row02_traceSegment_080_0702_0027, g32p_row02_traceSegment_080_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 648 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 648 54 54, g32p_row02_traceSegment_080_0648_0054, g32p_row02_traceSegment_080_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 756 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 756 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 756 13 14, g32p_row02_traceSegment_080_0756_0013, g32p_row02_traceSegment_080_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 796 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 783 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 783 13 14, g32p_row02_traceSegment_080_0783_0013, g32p_row02_traceSegment_080_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 756 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 756 27 27, g32p_row02_traceSegment_080_0756_0027, g32p_row02_traceSegment_080_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 810 13 14, g32p_row02_traceSegment_080_0810_0013, g32p_row02_traceSegment_080_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 850 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 837 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 837 13 14, g32p_row02_traceSegment_080_0837_0013, g32p_row02_traceSegment_080_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 810 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 810 27 27, g32p_row02_traceSegment_080_0810_0027, g32p_row02_traceSegment_080_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 756 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 756 54 54, g32p_row02_traceSegment_080_0756_0054, g32p_row02_traceSegment_080_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 648 216 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 648 108 108, g32p_row02_traceSegment_080_0648_0108, g32p_row02_traceSegment_080_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 432 432 = [16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 432 216 216, g32p_row02_traceSegment_080_0432_0216, g32p_row02_traceSegment_080_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_080 0 864 = [22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 432 432, g32p_row02_traceSegment_080_0000_0432, g32p_row02_traceSegment_080_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 864 13 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 864 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 864 13 14, g32p_row02_traceSegment_080_0864_0013, g32p_row02_traceSegment_080_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 904 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 891 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 891 13 14, g32p_row02_traceSegment_080_0891_0013, g32p_row02_traceSegment_080_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 864 54 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 864 27 27, g32p_row02_traceSegment_080_0864_0027, g32p_row02_traceSegment_080_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 918 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 918 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 918 13 14, g32p_row02_traceSegment_080_0918_0013, g32p_row02_traceSegment_080_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 945 13 14, g32p_row02_traceSegment_080_0945_0013, g32p_row02_traceSegment_080_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 918 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 918 27 27, g32p_row02_traceSegment_080_0918_0027, g32p_row02_traceSegment_080_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 864 108 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 864 54 54, g32p_row02_traceSegment_080_0864_0054, g32p_row02_traceSegment_080_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 972 13 14, g32p_row02_traceSegment_080_0972_0013, g32p_row02_traceSegment_080_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1012 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 999 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 999 13 14, g32p_row02_traceSegment_080_0999_0013, g32p_row02_traceSegment_080_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 972 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 972 27 27, g32p_row02_traceSegment_080_0972_0027, g32p_row02_traceSegment_080_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1026 13 14, g32p_row02_traceSegment_080_1026_0013, g32p_row02_traceSegment_080_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1053 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1053 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1053 13 14, g32p_row02_traceSegment_080_1053_0013, g32p_row02_traceSegment_080_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1026 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1026 27 27, g32p_row02_traceSegment_080_1026_0027, g32p_row02_traceSegment_080_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 972 108 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 972 54 54, g32p_row02_traceSegment_080_0972_0054, g32p_row02_traceSegment_080_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 864 216 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 864 108 108, g32p_row02_traceSegment_080_0864_0108, g32p_row02_traceSegment_080_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1093 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1080 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1080 13 14, g32p_row02_traceSegment_080_1080_0013, g32p_row02_traceSegment_080_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1120 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1107 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1107 13 14, g32p_row02_traceSegment_080_1107_0013, g32p_row02_traceSegment_080_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1080 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1080 27 27, g32p_row02_traceSegment_080_1080_0027, g32p_row02_traceSegment_080_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1147 14 = [2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1134 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1134 13 14, g32p_row02_traceSegment_080_1134_0013, g32p_row02_traceSegment_080_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1161 13 14, g32p_row02_traceSegment_080_1161_0013, g32p_row02_traceSegment_080_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1134 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1134 27 27, g32p_row02_traceSegment_080_1134_0027, g32p_row02_traceSegment_080_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1080 108 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1080 54 54, g32p_row02_traceSegment_080_1080_0054, g32p_row02_traceSegment_080_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1188 13 14, g32p_row02_traceSegment_080_1188_0013, g32p_row02_traceSegment_080_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1215 13 14, g32p_row02_traceSegment_080_1215_0013, g32p_row02_traceSegment_080_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1188 27 27, g32p_row02_traceSegment_080_1188_0027, g32p_row02_traceSegment_080_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1242 13 14, g32p_row02_traceSegment_080_1242_0013, g32p_row02_traceSegment_080_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1269 13 14, g32p_row02_traceSegment_080_1269_0013, g32p_row02_traceSegment_080_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1242 27 27, g32p_row02_traceSegment_080_1242_0027, g32p_row02_traceSegment_080_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1188 54 54, g32p_row02_traceSegment_080_1188_0054, g32p_row02_traceSegment_080_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 1080 216 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1080 108 108, g32p_row02_traceSegment_080_1080_0108, g32p_row02_traceSegment_080_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 864 432 = [12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 864 216 216, g32p_row02_traceSegment_080_0864_0216, g32p_row02_traceSegment_080_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1296 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1296 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1296 13 14, g32p_row02_traceSegment_080_1296_0013, g32p_row02_traceSegment_080_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1336 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1323 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1323 13 14, g32p_row02_traceSegment_080_1323_0013, g32p_row02_traceSegment_080_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1296 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1296 27 27, g32p_row02_traceSegment_080_1296_0027, g32p_row02_traceSegment_080_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1350 13 14, g32p_row02_traceSegment_080_1350_0013, g32p_row02_traceSegment_080_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1377 13 14, g32p_row02_traceSegment_080_1377_0013, g32p_row02_traceSegment_080_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1350 27 27, g32p_row02_traceSegment_080_1350_0027, g32p_row02_traceSegment_080_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1296 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1296 54 54, g32p_row02_traceSegment_080_1296_0054, g32p_row02_traceSegment_080_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1404 13 14, g32p_row02_traceSegment_080_1404_0013, g32p_row02_traceSegment_080_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1444 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1431 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1431 13 14, g32p_row02_traceSegment_080_1431_0013, g32p_row02_traceSegment_080_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1404 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1404 27 27, g32p_row02_traceSegment_080_1404_0027, g32p_row02_traceSegment_080_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1458 13 14, g32p_row02_traceSegment_080_1458_0013, g32p_row02_traceSegment_080_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1485 13 14, g32p_row02_traceSegment_080_1485_0013, g32p_row02_traceSegment_080_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1458 27 27, g32p_row02_traceSegment_080_1458_0027, g32p_row02_traceSegment_080_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1404 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1404 54 54, g32p_row02_traceSegment_080_1404_0054, g32p_row02_traceSegment_080_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 1296 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1296 108 108, g32p_row02_traceSegment_080_1296_0108, g32p_row02_traceSegment_080_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1525 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1512 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1512 13 14, g32p_row02_traceSegment_080_1512_0013, g32p_row02_traceSegment_080_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1539 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1539 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1539 13 14, g32p_row02_traceSegment_080_1539_0013, g32p_row02_traceSegment_080_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1512 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1512 27 27, g32p_row02_traceSegment_080_1512_0027, g32p_row02_traceSegment_080_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1566 13 14, g32p_row02_traceSegment_080_1566_0013, g32p_row02_traceSegment_080_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1593 13 14, g32p_row02_traceSegment_080_1593_0013, g32p_row02_traceSegment_080_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1566 27 27, g32p_row02_traceSegment_080_1566_0027, g32p_row02_traceSegment_080_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1512 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1512 54 54, g32p_row02_traceSegment_080_1512_0054, g32p_row02_traceSegment_080_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1620 13 14, g32p_row02_traceSegment_080_1620_0013, g32p_row02_traceSegment_080_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1647 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1647 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1647 13 14, g32p_row02_traceSegment_080_1647_0013, g32p_row02_traceSegment_080_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1620 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1620 27 27, g32p_row02_traceSegment_080_1620_0027, g32p_row02_traceSegment_080_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1674 13 14, g32p_row02_traceSegment_080_1674_0013, g32p_row02_traceSegment_080_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1701 13 14, g32p_row02_traceSegment_080_1701_0013, g32p_row02_traceSegment_080_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1674 27 27, g32p_row02_traceSegment_080_1674_0027, g32p_row02_traceSegment_080_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1620 54 54, g32p_row02_traceSegment_080_1620_0054, g32p_row02_traceSegment_080_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 1512 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1512 108 108, g32p_row02_traceSegment_080_1512_0108, g32p_row02_traceSegment_080_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 1296 432 = [6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1296 216 216, g32p_row02_traceSegment_080_1296_0216, g32p_row02_traceSegment_080_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_080 864 864 = [18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 864 432 432, g32p_row02_traceSegment_080_0864_0432, g32p_row02_traceSegment_080_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_080 0 1728 = [40] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 864 864, g32p_row02_traceSegment_080_0000_0864, g32p_row02_traceSegment_080_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1728 13 14, g32p_row02_traceSegment_080_1728_0013, g32p_row02_traceSegment_080_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1755 13 14, g32p_row02_traceSegment_080_1755_0013, g32p_row02_traceSegment_080_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1728 27 27, g32p_row02_traceSegment_080_1728_0027, g32p_row02_traceSegment_080_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1782 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1782 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1782 13 14, g32p_row02_traceSegment_080_1782_0013, g32p_row02_traceSegment_080_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1809 13 14, g32p_row02_traceSegment_080_1809_0013, g32p_row02_traceSegment_080_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1782 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1782 27 27, g32p_row02_traceSegment_080_1782_0027, g32p_row02_traceSegment_080_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1728 54 54, g32p_row02_traceSegment_080_1728_0054, g32p_row02_traceSegment_080_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1836 13 14, g32p_row02_traceSegment_080_1836_0013, g32p_row02_traceSegment_080_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1863 13 14, g32p_row02_traceSegment_080_1863_0013, g32p_row02_traceSegment_080_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1836 27 27, g32p_row02_traceSegment_080_1836_0027, g32p_row02_traceSegment_080_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1890 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1890 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1890 13 14, g32p_row02_traceSegment_080_1890_0013, g32p_row02_traceSegment_080_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1930 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1917 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1917 13 14, g32p_row02_traceSegment_080_1917_0013, g32p_row02_traceSegment_080_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1890 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1890 27 27, g32p_row02_traceSegment_080_1890_0027, g32p_row02_traceSegment_080_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1836 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1836 54 54, g32p_row02_traceSegment_080_1836_0054, g32p_row02_traceSegment_080_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1728 108 108, g32p_row02_traceSegment_080_1728_0108, g32p_row02_traceSegment_080_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1944 13 14, g32p_row02_traceSegment_080_1944_0013, g32p_row02_traceSegment_080_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1971 13 14, g32p_row02_traceSegment_080_1971_0013, g32p_row02_traceSegment_080_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1944 27 27, g32p_row02_traceSegment_080_1944_0027, g32p_row02_traceSegment_080_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1998 13 14, g32p_row02_traceSegment_080_1998_0013, g32p_row02_traceSegment_080_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2025 13 14, g32p_row02_traceSegment_080_2025_0013, g32p_row02_traceSegment_080_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1998 27 27, g32p_row02_traceSegment_080_1998_0027, g32p_row02_traceSegment_080_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1944 54 54, g32p_row02_traceSegment_080_1944_0054, g32p_row02_traceSegment_080_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2052 13 14, g32p_row02_traceSegment_080_2052_0013, g32p_row02_traceSegment_080_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2079 13 14, g32p_row02_traceSegment_080_2079_0013, g32p_row02_traceSegment_080_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2052 27 27, g32p_row02_traceSegment_080_2052_0027, g32p_row02_traceSegment_080_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2106 13 14, g32p_row02_traceSegment_080_2106_0013, g32p_row02_traceSegment_080_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2133 13 14, g32p_row02_traceSegment_080_2133_0013, g32p_row02_traceSegment_080_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2106 27 27, g32p_row02_traceSegment_080_2106_0027, g32p_row02_traceSegment_080_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2052 54 54, g32p_row02_traceSegment_080_2052_0054, g32p_row02_traceSegment_080_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1944 108 108, g32p_row02_traceSegment_080_1944_0108, g32p_row02_traceSegment_080_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1728 216 216, g32p_row02_traceSegment_080_1728_0216, g32p_row02_traceSegment_080_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2160 13 14, g32p_row02_traceSegment_080_2160_0013, g32p_row02_traceSegment_080_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2187 13 14, g32p_row02_traceSegment_080_2187_0013, g32p_row02_traceSegment_080_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2160 27 27, g32p_row02_traceSegment_080_2160_0027, g32p_row02_traceSegment_080_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2214 13 14, g32p_row02_traceSegment_080_2214_0013, g32p_row02_traceSegment_080_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2241 13 14, g32p_row02_traceSegment_080_2241_0013, g32p_row02_traceSegment_080_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2214 27 27, g32p_row02_traceSegment_080_2214_0027, g32p_row02_traceSegment_080_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2160 54 54, g32p_row02_traceSegment_080_2160_0054, g32p_row02_traceSegment_080_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2268 13 14, g32p_row02_traceSegment_080_2268_0013, g32p_row02_traceSegment_080_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2295 13 14, g32p_row02_traceSegment_080_2295_0013, g32p_row02_traceSegment_080_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2268 27 27, g32p_row02_traceSegment_080_2268_0027, g32p_row02_traceSegment_080_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2322 13 14, g32p_row02_traceSegment_080_2322_0013, g32p_row02_traceSegment_080_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2349 13 14, g32p_row02_traceSegment_080_2349_0013, g32p_row02_traceSegment_080_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2322 27 27, g32p_row02_traceSegment_080_2322_0027, g32p_row02_traceSegment_080_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2268 54 54, g32p_row02_traceSegment_080_2268_0054, g32p_row02_traceSegment_080_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2160 108 108, g32p_row02_traceSegment_080_2160_0108, g32p_row02_traceSegment_080_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2376 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2376 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2376 13 14, g32p_row02_traceSegment_080_2376_0013, g32p_row02_traceSegment_080_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2403 13 14, g32p_row02_traceSegment_080_2403_0013, g32p_row02_traceSegment_080_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2376 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2376 27 27, g32p_row02_traceSegment_080_2376_0027, g32p_row02_traceSegment_080_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2430 13 14, g32p_row02_traceSegment_080_2430_0013, g32p_row02_traceSegment_080_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2457 13 14, g32p_row02_traceSegment_080_2457_0013, g32p_row02_traceSegment_080_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2430 27 27, g32p_row02_traceSegment_080_2430_0027, g32p_row02_traceSegment_080_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2376 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2376 54 54, g32p_row02_traceSegment_080_2376_0054, g32p_row02_traceSegment_080_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2484 13 14, g32p_row02_traceSegment_080_2484_0013, g32p_row02_traceSegment_080_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2511 13 14, g32p_row02_traceSegment_080_2511_0013, g32p_row02_traceSegment_080_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2484 27 27, g32p_row02_traceSegment_080_2484_0027, g32p_row02_traceSegment_080_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2538 13 14, g32p_row02_traceSegment_080_2538_0013, g32p_row02_traceSegment_080_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2565 13 14, g32p_row02_traceSegment_080_2565_0013, g32p_row02_traceSegment_080_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2538 27 27, g32p_row02_traceSegment_080_2538_0027, g32p_row02_traceSegment_080_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2484 54 54, g32p_row02_traceSegment_080_2484_0054, g32p_row02_traceSegment_080_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 2376 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2376 108 108, g32p_row02_traceSegment_080_2376_0108, g32p_row02_traceSegment_080_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 2160 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2160 216 216, g32p_row02_traceSegment_080_2160_0216, g32p_row02_traceSegment_080_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1728 432 432, g32p_row02_traceSegment_080_1728_0432, g32p_row02_traceSegment_080_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2592 13 14, g32p_row02_traceSegment_080_2592_0013, g32p_row02_traceSegment_080_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2619 13 14, g32p_row02_traceSegment_080_2619_0013, g32p_row02_traceSegment_080_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2592 27 27, g32p_row02_traceSegment_080_2592_0027, g32p_row02_traceSegment_080_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2646 13 14, g32p_row02_traceSegment_080_2646_0013, g32p_row02_traceSegment_080_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2673 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2673 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2673 13 14, g32p_row02_traceSegment_080_2673_0013, g32p_row02_traceSegment_080_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2646 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2646 27 27, g32p_row02_traceSegment_080_2646_0027, g32p_row02_traceSegment_080_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2592 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2592 54 54, g32p_row02_traceSegment_080_2592_0054, g32p_row02_traceSegment_080_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2700 13 14, g32p_row02_traceSegment_080_2700_0013, g32p_row02_traceSegment_080_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2727 13 14, g32p_row02_traceSegment_080_2727_0013, g32p_row02_traceSegment_080_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2700 27 27, g32p_row02_traceSegment_080_2700_0027, g32p_row02_traceSegment_080_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2754 13 14, g32p_row02_traceSegment_080_2754_0013, g32p_row02_traceSegment_080_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2781 13 14, g32p_row02_traceSegment_080_2781_0013, g32p_row02_traceSegment_080_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2754 27 27, g32p_row02_traceSegment_080_2754_0027, g32p_row02_traceSegment_080_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2700 54 54, g32p_row02_traceSegment_080_2700_0054, g32p_row02_traceSegment_080_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 2592 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2592 108 108, g32p_row02_traceSegment_080_2592_0108, g32p_row02_traceSegment_080_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2808 13 14, g32p_row02_traceSegment_080_2808_0013, g32p_row02_traceSegment_080_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2835 13 14, g32p_row02_traceSegment_080_2835_0013, g32p_row02_traceSegment_080_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2808 27 27, g32p_row02_traceSegment_080_2808_0027, g32p_row02_traceSegment_080_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2862 13 14, g32p_row02_traceSegment_080_2862_0013, g32p_row02_traceSegment_080_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2889 13 14, g32p_row02_traceSegment_080_2889_0013, g32p_row02_traceSegment_080_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2862 27 27, g32p_row02_traceSegment_080_2862_0027, g32p_row02_traceSegment_080_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2808 54 54, g32p_row02_traceSegment_080_2808_0054, g32p_row02_traceSegment_080_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2916 13 14, g32p_row02_traceSegment_080_2916_0013, g32p_row02_traceSegment_080_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2943 13 14, g32p_row02_traceSegment_080_2943_0013, g32p_row02_traceSegment_080_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2916 27 27, g32p_row02_traceSegment_080_2916_0027, g32p_row02_traceSegment_080_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2970 13 14, g32p_row02_traceSegment_080_2970_0013, g32p_row02_traceSegment_080_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3010 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 2997 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2997 13 14, g32p_row02_traceSegment_080_2997_0013, g32p_row02_traceSegment_080_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 2970 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2970 27 27, g32p_row02_traceSegment_080_2970_0027, g32p_row02_traceSegment_080_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 2916 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2916 54 54, g32p_row02_traceSegment_080_2916_0054, g32p_row02_traceSegment_080_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 2808 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2808 108 108, g32p_row02_traceSegment_080_2808_0108, g32p_row02_traceSegment_080_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 2592 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2592 216 216, g32p_row02_traceSegment_080_2592_0216, g32p_row02_traceSegment_080_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3024 13 14, g32p_row02_traceSegment_080_3024_0013, g32p_row02_traceSegment_080_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3051 13 14, g32p_row02_traceSegment_080_3051_0013, g32p_row02_traceSegment_080_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3024 27 27, g32p_row02_traceSegment_080_3024_0027, g32p_row02_traceSegment_080_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3078 13 14, g32p_row02_traceSegment_080_3078_0013, g32p_row02_traceSegment_080_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3105 13 14, g32p_row02_traceSegment_080_3105_0013, g32p_row02_traceSegment_080_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3078 27 27, g32p_row02_traceSegment_080_3078_0027, g32p_row02_traceSegment_080_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3024 54 54, g32p_row02_traceSegment_080_3024_0054, g32p_row02_traceSegment_080_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3132 13 14, g32p_row02_traceSegment_080_3132_0013, g32p_row02_traceSegment_080_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3172 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3159 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3159 13 14, g32p_row02_traceSegment_080_3159_0013, g32p_row02_traceSegment_080_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3132 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3132 27 27, g32p_row02_traceSegment_080_3132_0027, g32p_row02_traceSegment_080_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3186 13 14, g32p_row02_traceSegment_080_3186_0013, g32p_row02_traceSegment_080_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3213 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3213 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3213 13 14, g32p_row02_traceSegment_080_3213_0013, g32p_row02_traceSegment_080_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3186 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3186 27 27, g32p_row02_traceSegment_080_3186_0027, g32p_row02_traceSegment_080_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 3132 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3132 54 54, g32p_row02_traceSegment_080_3132_0054, g32p_row02_traceSegment_080_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 3024 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3024 108 108, g32p_row02_traceSegment_080_3024_0108, g32p_row02_traceSegment_080_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3240 13 14, g32p_row02_traceSegment_080_3240_0013, g32p_row02_traceSegment_080_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3267 13 14, g32p_row02_traceSegment_080_3267_0013, g32p_row02_traceSegment_080_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3240 27 27, g32p_row02_traceSegment_080_3240_0027, g32p_row02_traceSegment_080_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3294 13 14, g32p_row02_traceSegment_080_3294_0013, g32p_row02_traceSegment_080_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3321 13 14, g32p_row02_traceSegment_080_3321_0013, g32p_row02_traceSegment_080_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3294 27 27, g32p_row02_traceSegment_080_3294_0027, g32p_row02_traceSegment_080_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3240 54 54, g32p_row02_traceSegment_080_3240_0054, g32p_row02_traceSegment_080_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3348 13 14, g32p_row02_traceSegment_080_3348_0013, g32p_row02_traceSegment_080_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3375 13 14, g32p_row02_traceSegment_080_3375_0013, g32p_row02_traceSegment_080_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3348 27 27, g32p_row02_traceSegment_080_3348_0027, g32p_row02_traceSegment_080_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3402 13 14, g32p_row02_traceSegment_080_3402_0013, g32p_row02_traceSegment_080_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_080 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_080 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_080_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_080 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3429 13 14, g32p_row02_traceSegment_080_3429_0013, g32p_row02_traceSegment_080_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_080 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3402 27 27, g32p_row02_traceSegment_080_3402_0027, g32p_row02_traceSegment_080_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_080 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3348 54 54, g32p_row02_traceSegment_080_3348_0054, g32p_row02_traceSegment_080_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_080 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3240 108 108, g32p_row02_traceSegment_080_3240_0108, g32p_row02_traceSegment_080_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_080_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_080 3024 432 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 3024 216 216, g32p_row02_traceSegment_080_3024_0216, g32p_row02_traceSegment_080_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_080_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_080 2592 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 2592 432 432, g32p_row02_traceSegment_080_2592_0432, g32p_row02_traceSegment_080_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_080_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_080 1728 1728 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 1728 864 864, g32p_row02_traceSegment_080_1728_0864, g32p_row02_traceSegment_080_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_080_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_080 0 3456 = [48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_080 0 1728 1728, g32p_row02_traceSegment_080_0000_1728, g32p_row02_traceSegment_080_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_080 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 80 = [48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_080_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_081 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 81 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_081_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 13 14, g32p_row02_traceSegment_081_0000_0013, g32p_row02_traceSegment_081_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 27 13 14, g32p_row02_traceSegment_081_0027_0013, g32p_row02_traceSegment_081_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 27 27, g32p_row02_traceSegment_081_0000_0027, g32p_row02_traceSegment_081_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 54 13 14, g32p_row02_traceSegment_081_0054_0013, g32p_row02_traceSegment_081_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 81 13 14, g32p_row02_traceSegment_081_0081_0013, g32p_row02_traceSegment_081_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 54 27 27, g32p_row02_traceSegment_081_0054_0027, g32p_row02_traceSegment_081_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 54 54, g32p_row02_traceSegment_081_0000_0054, g32p_row02_traceSegment_081_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 108 13 14, g32p_row02_traceSegment_081_0108_0013, g32p_row02_traceSegment_081_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 135 13 14, g32p_row02_traceSegment_081_0135_0013, g32p_row02_traceSegment_081_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 108 27 27, g32p_row02_traceSegment_081_0108_0027, g32p_row02_traceSegment_081_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 162 13 14, g32p_row02_traceSegment_081_0162_0013, g32p_row02_traceSegment_081_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 189 13 14, g32p_row02_traceSegment_081_0189_0013, g32p_row02_traceSegment_081_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 162 27 27, g32p_row02_traceSegment_081_0162_0027, g32p_row02_traceSegment_081_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 108 54 54, g32p_row02_traceSegment_081_0108_0054, g32p_row02_traceSegment_081_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 108 108, g32p_row02_traceSegment_081_0000_0108, g32p_row02_traceSegment_081_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 216 13 14, g32p_row02_traceSegment_081_0216_0013, g32p_row02_traceSegment_081_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 243 13 14, g32p_row02_traceSegment_081_0243_0013, g32p_row02_traceSegment_081_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 216 27 27, g32p_row02_traceSegment_081_0216_0027, g32p_row02_traceSegment_081_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 270 13 14, g32p_row02_traceSegment_081_0270_0013, g32p_row02_traceSegment_081_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 297 13 14, g32p_row02_traceSegment_081_0297_0013, g32p_row02_traceSegment_081_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 270 27 27, g32p_row02_traceSegment_081_0270_0027, g32p_row02_traceSegment_081_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 216 54 54, g32p_row02_traceSegment_081_0216_0054, g32p_row02_traceSegment_081_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 324 13 14, g32p_row02_traceSegment_081_0324_0013, g32p_row02_traceSegment_081_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 351 13 14, g32p_row02_traceSegment_081_0351_0013, g32p_row02_traceSegment_081_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 324 27 27, g32p_row02_traceSegment_081_0324_0027, g32p_row02_traceSegment_081_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 378 13 14, g32p_row02_traceSegment_081_0378_0013, g32p_row02_traceSegment_081_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 405 13 14, g32p_row02_traceSegment_081_0405_0013, g32p_row02_traceSegment_081_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 378 27 27, g32p_row02_traceSegment_081_0378_0027, g32p_row02_traceSegment_081_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 324 54 54, g32p_row02_traceSegment_081_0324_0054, g32p_row02_traceSegment_081_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 216 108 108, g32p_row02_traceSegment_081_0216_0108, g32p_row02_traceSegment_081_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 216 216, g32p_row02_traceSegment_081_0000_0216, g32p_row02_traceSegment_081_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 432 13 14, g32p_row02_traceSegment_081_0432_0013, g32p_row02_traceSegment_081_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 459 13 14, g32p_row02_traceSegment_081_0459_0013, g32p_row02_traceSegment_081_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 432 27 27, g32p_row02_traceSegment_081_0432_0027, g32p_row02_traceSegment_081_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 486 13 14, g32p_row02_traceSegment_081_0486_0013, g32p_row02_traceSegment_081_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 513 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 526 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 513 27 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 513 13 14, g32p_row02_traceSegment_081_0513_0013, g32p_row02_traceSegment_081_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 486 54 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 486 27 27, g32p_row02_traceSegment_081_0486_0027, g32p_row02_traceSegment_081_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 432 108 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 432 54 54, g32p_row02_traceSegment_081_0432_0054, g32p_row02_traceSegment_081_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 540 13 14, g32p_row02_traceSegment_081_0540_0013, g32p_row02_traceSegment_081_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 567 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 567 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 567 13 14, g32p_row02_traceSegment_081_0567_0013, g32p_row02_traceSegment_081_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 540 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 540 27 27, g32p_row02_traceSegment_081_0540_0027, g32p_row02_traceSegment_081_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 594 13 14, g32p_row02_traceSegment_081_0594_0013, g32p_row02_traceSegment_081_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 621 13 14, g32p_row02_traceSegment_081_0621_0013, g32p_row02_traceSegment_081_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 594 27 27, g32p_row02_traceSegment_081_0594_0027, g32p_row02_traceSegment_081_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 540 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 540 54 54, g32p_row02_traceSegment_081_0540_0054, g32p_row02_traceSegment_081_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 432 216 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 432 108 108, g32p_row02_traceSegment_081_0432_0108, g32p_row02_traceSegment_081_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 648 13 14, g32p_row02_traceSegment_081_0648_0013, g32p_row02_traceSegment_081_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 675 13 14, g32p_row02_traceSegment_081_0675_0013, g32p_row02_traceSegment_081_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 648 27 27, g32p_row02_traceSegment_081_0648_0027, g32p_row02_traceSegment_081_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 715 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 702 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 702 13 14, g32p_row02_traceSegment_081_0702_0013, g32p_row02_traceSegment_081_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 729 13 14, g32p_row02_traceSegment_081_0729_0013, g32p_row02_traceSegment_081_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 702 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 702 27 27, g32p_row02_traceSegment_081_0702_0027, g32p_row02_traceSegment_081_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 648 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 648 54 54, g32p_row02_traceSegment_081_0648_0054, g32p_row02_traceSegment_081_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 756 13 14, g32p_row02_traceSegment_081_0756_0013, g32p_row02_traceSegment_081_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 783 13 14, g32p_row02_traceSegment_081_0783_0013, g32p_row02_traceSegment_081_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 756 27 27, g32p_row02_traceSegment_081_0756_0027, g32p_row02_traceSegment_081_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 810 13 14, g32p_row02_traceSegment_081_0810_0013, g32p_row02_traceSegment_081_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 837 13 14, g32p_row02_traceSegment_081_0837_0013, g32p_row02_traceSegment_081_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 810 27 27, g32p_row02_traceSegment_081_0810_0027, g32p_row02_traceSegment_081_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 756 54 54, g32p_row02_traceSegment_081_0756_0054, g32p_row02_traceSegment_081_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 648 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 648 108 108, g32p_row02_traceSegment_081_0648_0108, g32p_row02_traceSegment_081_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 432 432 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 432 216 216, g32p_row02_traceSegment_081_0432_0216, g32p_row02_traceSegment_081_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_081 0 864 = [4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 432 432, g32p_row02_traceSegment_081_0000_0432, g32p_row02_traceSegment_081_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 864 13 14, g32p_row02_traceSegment_081_0864_0013, g32p_row02_traceSegment_081_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 891 13 14, g32p_row02_traceSegment_081_0891_0013, g32p_row02_traceSegment_081_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 864 27 27, g32p_row02_traceSegment_081_0864_0027, g32p_row02_traceSegment_081_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 918 13 14, g32p_row02_traceSegment_081_0918_0013, g32p_row02_traceSegment_081_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 945 13 14, g32p_row02_traceSegment_081_0945_0013, g32p_row02_traceSegment_081_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 918 27 27, g32p_row02_traceSegment_081_0918_0027, g32p_row02_traceSegment_081_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 864 54 54, g32p_row02_traceSegment_081_0864_0054, g32p_row02_traceSegment_081_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 972 13 14, g32p_row02_traceSegment_081_0972_0013, g32p_row02_traceSegment_081_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 999 13 14, g32p_row02_traceSegment_081_0999_0013, g32p_row02_traceSegment_081_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 972 27 27, g32p_row02_traceSegment_081_0972_0027, g32p_row02_traceSegment_081_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1026 13 14, g32p_row02_traceSegment_081_1026_0013, g32p_row02_traceSegment_081_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1053 13 14, g32p_row02_traceSegment_081_1053_0013, g32p_row02_traceSegment_081_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1026 27 27, g32p_row02_traceSegment_081_1026_0027, g32p_row02_traceSegment_081_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 972 54 54, g32p_row02_traceSegment_081_0972_0054, g32p_row02_traceSegment_081_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 864 108 108, g32p_row02_traceSegment_081_0864_0108, g32p_row02_traceSegment_081_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1080 13 14, g32p_row02_traceSegment_081_1080_0013, g32p_row02_traceSegment_081_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1107 13 14, g32p_row02_traceSegment_081_1107_0013, g32p_row02_traceSegment_081_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1080 27 27, g32p_row02_traceSegment_081_1080_0027, g32p_row02_traceSegment_081_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1134 13 14, g32p_row02_traceSegment_081_1134_0013, g32p_row02_traceSegment_081_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1161 13 14, g32p_row02_traceSegment_081_1161_0013, g32p_row02_traceSegment_081_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1134 27 27, g32p_row02_traceSegment_081_1134_0027, g32p_row02_traceSegment_081_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1080 54 54, g32p_row02_traceSegment_081_1080_0054, g32p_row02_traceSegment_081_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1188 13 14, g32p_row02_traceSegment_081_1188_0013, g32p_row02_traceSegment_081_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1215 13 14, g32p_row02_traceSegment_081_1215_0013, g32p_row02_traceSegment_081_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1188 27 27, g32p_row02_traceSegment_081_1188_0027, g32p_row02_traceSegment_081_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1242 13 14, g32p_row02_traceSegment_081_1242_0013, g32p_row02_traceSegment_081_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1269 13 14, g32p_row02_traceSegment_081_1269_0013, g32p_row02_traceSegment_081_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1242 27 27, g32p_row02_traceSegment_081_1242_0027, g32p_row02_traceSegment_081_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1188 54 54, g32p_row02_traceSegment_081_1188_0054, g32p_row02_traceSegment_081_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1080 108 108, g32p_row02_traceSegment_081_1080_0108, g32p_row02_traceSegment_081_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 864 216 216, g32p_row02_traceSegment_081_0864_0216, g32p_row02_traceSegment_081_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1296 13 14, g32p_row02_traceSegment_081_1296_0013, g32p_row02_traceSegment_081_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1323 13 14, g32p_row02_traceSegment_081_1323_0013, g32p_row02_traceSegment_081_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1296 27 27, g32p_row02_traceSegment_081_1296_0027, g32p_row02_traceSegment_081_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1350 13 14, g32p_row02_traceSegment_081_1350_0013, g32p_row02_traceSegment_081_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1377 13 14, g32p_row02_traceSegment_081_1377_0013, g32p_row02_traceSegment_081_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1350 27 27, g32p_row02_traceSegment_081_1350_0027, g32p_row02_traceSegment_081_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1296 54 54, g32p_row02_traceSegment_081_1296_0054, g32p_row02_traceSegment_081_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1404 13 14, g32p_row02_traceSegment_081_1404_0013, g32p_row02_traceSegment_081_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1431 13 14, g32p_row02_traceSegment_081_1431_0013, g32p_row02_traceSegment_081_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1404 27 27, g32p_row02_traceSegment_081_1404_0027, g32p_row02_traceSegment_081_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1458 13 14, g32p_row02_traceSegment_081_1458_0013, g32p_row02_traceSegment_081_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1485 13 14, g32p_row02_traceSegment_081_1485_0013, g32p_row02_traceSegment_081_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1458 27 27, g32p_row02_traceSegment_081_1458_0027, g32p_row02_traceSegment_081_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1404 54 54, g32p_row02_traceSegment_081_1404_0054, g32p_row02_traceSegment_081_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1296 108 108, g32p_row02_traceSegment_081_1296_0108, g32p_row02_traceSegment_081_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1512 13 14, g32p_row02_traceSegment_081_1512_0013, g32p_row02_traceSegment_081_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1539 13 14, g32p_row02_traceSegment_081_1539_0013, g32p_row02_traceSegment_081_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1512 27 27, g32p_row02_traceSegment_081_1512_0027, g32p_row02_traceSegment_081_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1566 13 14, g32p_row02_traceSegment_081_1566_0013, g32p_row02_traceSegment_081_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1593 13 14, g32p_row02_traceSegment_081_1593_0013, g32p_row02_traceSegment_081_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1566 27 27, g32p_row02_traceSegment_081_1566_0027, g32p_row02_traceSegment_081_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1512 54 54, g32p_row02_traceSegment_081_1512_0054, g32p_row02_traceSegment_081_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1620 13 14, g32p_row02_traceSegment_081_1620_0013, g32p_row02_traceSegment_081_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1660 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1647 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1647 13 14, g32p_row02_traceSegment_081_1647_0013, g32p_row02_traceSegment_081_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1620 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1620 27 27, g32p_row02_traceSegment_081_1620_0027, g32p_row02_traceSegment_081_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1674 13 14, g32p_row02_traceSegment_081_1674_0013, g32p_row02_traceSegment_081_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1701 13 14, g32p_row02_traceSegment_081_1701_0013, g32p_row02_traceSegment_081_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1674 27 27, g32p_row02_traceSegment_081_1674_0027, g32p_row02_traceSegment_081_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1620 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1620 54 54, g32p_row02_traceSegment_081_1620_0054, g32p_row02_traceSegment_081_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 1512 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1512 108 108, g32p_row02_traceSegment_081_1512_0108, g32p_row02_traceSegment_081_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 1296 432 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1296 216 216, g32p_row02_traceSegment_081_1296_0216, g32p_row02_traceSegment_081_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_081 864 864 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 864 432 432, g32p_row02_traceSegment_081_0864_0432, g32p_row02_traceSegment_081_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_081 0 1728 = [5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 864 864, g32p_row02_traceSegment_081_0000_0864, g32p_row02_traceSegment_081_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1728 13 14, g32p_row02_traceSegment_081_1728_0013, g32p_row02_traceSegment_081_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1755 13 14, g32p_row02_traceSegment_081_1755_0013, g32p_row02_traceSegment_081_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1728 27 27, g32p_row02_traceSegment_081_1728_0027, g32p_row02_traceSegment_081_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1782 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1782 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1782 13 14, g32p_row02_traceSegment_081_1782_0013, g32p_row02_traceSegment_081_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1809 13 14, g32p_row02_traceSegment_081_1809_0013, g32p_row02_traceSegment_081_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1782 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1782 27 27, g32p_row02_traceSegment_081_1782_0027, g32p_row02_traceSegment_081_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1728 54 54, g32p_row02_traceSegment_081_1728_0054, g32p_row02_traceSegment_081_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1836 13 14, g32p_row02_traceSegment_081_1836_0013, g32p_row02_traceSegment_081_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1863 13 14, g32p_row02_traceSegment_081_1863_0013, g32p_row02_traceSegment_081_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1836 27 27, g32p_row02_traceSegment_081_1836_0027, g32p_row02_traceSegment_081_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1890 13 14, g32p_row02_traceSegment_081_1890_0013, g32p_row02_traceSegment_081_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1930 14 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1917 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1917 13 14, g32p_row02_traceSegment_081_1917_0013, g32p_row02_traceSegment_081_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1890 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1890 27 27, g32p_row02_traceSegment_081_1890_0027, g32p_row02_traceSegment_081_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1836 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1836 54 54, g32p_row02_traceSegment_081_1836_0054, g32p_row02_traceSegment_081_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 216 = [2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1728 108 108, g32p_row02_traceSegment_081_1728_0108, g32p_row02_traceSegment_081_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1944 13 14, g32p_row02_traceSegment_081_1944_0013, g32p_row02_traceSegment_081_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1971 13 = [1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1971 27 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1971 13 14, g32p_row02_traceSegment_081_1971_0013, g32p_row02_traceSegment_081_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1944 54 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1944 27 27, g32p_row02_traceSegment_081_1944_0027, g32p_row02_traceSegment_081_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1998 13 14, g32p_row02_traceSegment_081_1998_0013, g32p_row02_traceSegment_081_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2025 13 14, g32p_row02_traceSegment_081_2025_0013, g32p_row02_traceSegment_081_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1998 27 27, g32p_row02_traceSegment_081_1998_0027, g32p_row02_traceSegment_081_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 1944 108 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1944 54 54, g32p_row02_traceSegment_081_1944_0054, g32p_row02_traceSegment_081_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2052 13 14, g32p_row02_traceSegment_081_2052_0013, g32p_row02_traceSegment_081_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2079 13 14, g32p_row02_traceSegment_081_2079_0013, g32p_row02_traceSegment_081_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2052 27 27, g32p_row02_traceSegment_081_2052_0027, g32p_row02_traceSegment_081_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2106 13 14, g32p_row02_traceSegment_081_2106_0013, g32p_row02_traceSegment_081_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2133 13 14, g32p_row02_traceSegment_081_2133_0013, g32p_row02_traceSegment_081_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2106 27 27, g32p_row02_traceSegment_081_2106_0027, g32p_row02_traceSegment_081_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2052 54 54, g32p_row02_traceSegment_081_2052_0054, g32p_row02_traceSegment_081_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 1944 216 = [1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1944 108 108, g32p_row02_traceSegment_081_1944_0108, g32p_row02_traceSegment_081_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 432 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1728 216 216, g32p_row02_traceSegment_081_1728_0216, g32p_row02_traceSegment_081_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2160 13 14, g32p_row02_traceSegment_081_2160_0013, g32p_row02_traceSegment_081_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2187 13 14, g32p_row02_traceSegment_081_2187_0013, g32p_row02_traceSegment_081_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2160 27 27, g32p_row02_traceSegment_081_2160_0027, g32p_row02_traceSegment_081_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2214 13 14, g32p_row02_traceSegment_081_2214_0013, g32p_row02_traceSegment_081_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2241 13 14, g32p_row02_traceSegment_081_2241_0013, g32p_row02_traceSegment_081_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2214 27 27, g32p_row02_traceSegment_081_2214_0027, g32p_row02_traceSegment_081_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2160 54 54, g32p_row02_traceSegment_081_2160_0054, g32p_row02_traceSegment_081_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2268 13 14, g32p_row02_traceSegment_081_2268_0013, g32p_row02_traceSegment_081_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2295 13 14, g32p_row02_traceSegment_081_2295_0013, g32p_row02_traceSegment_081_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2268 27 27, g32p_row02_traceSegment_081_2268_0027, g32p_row02_traceSegment_081_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2322 13 14, g32p_row02_traceSegment_081_2322_0013, g32p_row02_traceSegment_081_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2349 13 14, g32p_row02_traceSegment_081_2349_0013, g32p_row02_traceSegment_081_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2322 27 27, g32p_row02_traceSegment_081_2322_0027, g32p_row02_traceSegment_081_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2268 54 54, g32p_row02_traceSegment_081_2268_0054, g32p_row02_traceSegment_081_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2160 108 108, g32p_row02_traceSegment_081_2160_0108, g32p_row02_traceSegment_081_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2376 13 14, g32p_row02_traceSegment_081_2376_0013, g32p_row02_traceSegment_081_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2403 13 14, g32p_row02_traceSegment_081_2403_0013, g32p_row02_traceSegment_081_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2376 27 27, g32p_row02_traceSegment_081_2376_0027, g32p_row02_traceSegment_081_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2430 13 14, g32p_row02_traceSegment_081_2430_0013, g32p_row02_traceSegment_081_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2457 13 14, g32p_row02_traceSegment_081_2457_0013, g32p_row02_traceSegment_081_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2430 27 27, g32p_row02_traceSegment_081_2430_0027, g32p_row02_traceSegment_081_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2376 54 54, g32p_row02_traceSegment_081_2376_0054, g32p_row02_traceSegment_081_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2484 13 14, g32p_row02_traceSegment_081_2484_0013, g32p_row02_traceSegment_081_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2511 13 14, g32p_row02_traceSegment_081_2511_0013, g32p_row02_traceSegment_081_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2484 27 27, g32p_row02_traceSegment_081_2484_0027, g32p_row02_traceSegment_081_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2538 13 14, g32p_row02_traceSegment_081_2538_0013, g32p_row02_traceSegment_081_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2565 13 14, g32p_row02_traceSegment_081_2565_0013, g32p_row02_traceSegment_081_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2538 27 27, g32p_row02_traceSegment_081_2538_0027, g32p_row02_traceSegment_081_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2484 54 54, g32p_row02_traceSegment_081_2484_0054, g32p_row02_traceSegment_081_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2376 108 108, g32p_row02_traceSegment_081_2376_0108, g32p_row02_traceSegment_081_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2160 216 216, g32p_row02_traceSegment_081_2160_0216, g32p_row02_traceSegment_081_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 864 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1728 432 432, g32p_row02_traceSegment_081_1728_0432, g32p_row02_traceSegment_081_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2592 13 14, g32p_row02_traceSegment_081_2592_0013, g32p_row02_traceSegment_081_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2619 13 14, g32p_row02_traceSegment_081_2619_0013, g32p_row02_traceSegment_081_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2592 27 27, g32p_row02_traceSegment_081_2592_0027, g32p_row02_traceSegment_081_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2646 13 14, g32p_row02_traceSegment_081_2646_0013, g32p_row02_traceSegment_081_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2673 13 14, g32p_row02_traceSegment_081_2673_0013, g32p_row02_traceSegment_081_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2646 27 27, g32p_row02_traceSegment_081_2646_0027, g32p_row02_traceSegment_081_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2592 54 54, g32p_row02_traceSegment_081_2592_0054, g32p_row02_traceSegment_081_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2700 13 14, g32p_row02_traceSegment_081_2700_0013, g32p_row02_traceSegment_081_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2727 13 14, g32p_row02_traceSegment_081_2727_0013, g32p_row02_traceSegment_081_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2700 27 27, g32p_row02_traceSegment_081_2700_0027, g32p_row02_traceSegment_081_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2754 13 14, g32p_row02_traceSegment_081_2754_0013, g32p_row02_traceSegment_081_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2781 13 14, g32p_row02_traceSegment_081_2781_0013, g32p_row02_traceSegment_081_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2754 27 27, g32p_row02_traceSegment_081_2754_0027, g32p_row02_traceSegment_081_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2700 54 54, g32p_row02_traceSegment_081_2700_0054, g32p_row02_traceSegment_081_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2592 108 108, g32p_row02_traceSegment_081_2592_0108, g32p_row02_traceSegment_081_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2808 13 14, g32p_row02_traceSegment_081_2808_0013, g32p_row02_traceSegment_081_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2835 13 14, g32p_row02_traceSegment_081_2835_0013, g32p_row02_traceSegment_081_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2808 27 27, g32p_row02_traceSegment_081_2808_0027, g32p_row02_traceSegment_081_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2862 13 14, g32p_row02_traceSegment_081_2862_0013, g32p_row02_traceSegment_081_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2889 13 14, g32p_row02_traceSegment_081_2889_0013, g32p_row02_traceSegment_081_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2862 27 27, g32p_row02_traceSegment_081_2862_0027, g32p_row02_traceSegment_081_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2808 54 54, g32p_row02_traceSegment_081_2808_0054, g32p_row02_traceSegment_081_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2916 13 14, g32p_row02_traceSegment_081_2916_0013, g32p_row02_traceSegment_081_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2943 13 14, g32p_row02_traceSegment_081_2943_0013, g32p_row02_traceSegment_081_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2916 27 27, g32p_row02_traceSegment_081_2916_0027, g32p_row02_traceSegment_081_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2970 13 14, g32p_row02_traceSegment_081_2970_0013, g32p_row02_traceSegment_081_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2997 13 14, g32p_row02_traceSegment_081_2997_0013, g32p_row02_traceSegment_081_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2970 27 27, g32p_row02_traceSegment_081_2970_0027, g32p_row02_traceSegment_081_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2916 54 54, g32p_row02_traceSegment_081_2916_0054, g32p_row02_traceSegment_081_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2808 108 108, g32p_row02_traceSegment_081_2808_0108, g32p_row02_traceSegment_081_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 2592 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2592 216 216, g32p_row02_traceSegment_081_2592_0216, g32p_row02_traceSegment_081_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3024 13 14, g32p_row02_traceSegment_081_3024_0013, g32p_row02_traceSegment_081_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3051 13 14, g32p_row02_traceSegment_081_3051_0013, g32p_row02_traceSegment_081_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3024 27 27, g32p_row02_traceSegment_081_3024_0027, g32p_row02_traceSegment_081_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3078 13 14, g32p_row02_traceSegment_081_3078_0013, g32p_row02_traceSegment_081_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3105 13 14, g32p_row02_traceSegment_081_3105_0013, g32p_row02_traceSegment_081_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3078 27 27, g32p_row02_traceSegment_081_3078_0027, g32p_row02_traceSegment_081_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3024 54 54, g32p_row02_traceSegment_081_3024_0054, g32p_row02_traceSegment_081_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3132 13 14, g32p_row02_traceSegment_081_3132_0013, g32p_row02_traceSegment_081_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3159 13 14, g32p_row02_traceSegment_081_3159_0013, g32p_row02_traceSegment_081_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3132 27 27, g32p_row02_traceSegment_081_3132_0027, g32p_row02_traceSegment_081_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3186 13 14, g32p_row02_traceSegment_081_3186_0013, g32p_row02_traceSegment_081_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3213 13 14, g32p_row02_traceSegment_081_3213_0013, g32p_row02_traceSegment_081_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3186 27 27, g32p_row02_traceSegment_081_3186_0027, g32p_row02_traceSegment_081_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3132 54 54, g32p_row02_traceSegment_081_3132_0054, g32p_row02_traceSegment_081_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3024 108 108, g32p_row02_traceSegment_081_3024_0108, g32p_row02_traceSegment_081_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3240 13 14, g32p_row02_traceSegment_081_3240_0013, g32p_row02_traceSegment_081_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3267 13 14, g32p_row02_traceSegment_081_3267_0013, g32p_row02_traceSegment_081_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3240 27 27, g32p_row02_traceSegment_081_3240_0027, g32p_row02_traceSegment_081_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3294 13 14, g32p_row02_traceSegment_081_3294_0013, g32p_row02_traceSegment_081_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3321 13 14, g32p_row02_traceSegment_081_3321_0013, g32p_row02_traceSegment_081_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3294 27 27, g32p_row02_traceSegment_081_3294_0027, g32p_row02_traceSegment_081_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3240 54 54, g32p_row02_traceSegment_081_3240_0054, g32p_row02_traceSegment_081_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3348 13 14, g32p_row02_traceSegment_081_3348_0013, g32p_row02_traceSegment_081_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3375 13 14, g32p_row02_traceSegment_081_3375_0013, g32p_row02_traceSegment_081_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3348 27 27, g32p_row02_traceSegment_081_3348_0027, g32p_row02_traceSegment_081_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3402 13 14, g32p_row02_traceSegment_081_3402_0013, g32p_row02_traceSegment_081_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_081 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_081 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_081_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_081 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3429 13 14, g32p_row02_traceSegment_081_3429_0013, g32p_row02_traceSegment_081_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_081 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3402 27 27, g32p_row02_traceSegment_081_3402_0027, g32p_row02_traceSegment_081_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_081 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3348 54 54, g32p_row02_traceSegment_081_3348_0054, g32p_row02_traceSegment_081_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_081 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3240 108 108, g32p_row02_traceSegment_081_3240_0108, g32p_row02_traceSegment_081_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_081_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_081 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 3024 216 216, g32p_row02_traceSegment_081_3024_0216, g32p_row02_traceSegment_081_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_081_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_081 2592 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 2592 432 432, g32p_row02_traceSegment_081_2592_0432, g32p_row02_traceSegment_081_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_081_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_081 1728 1728 = [3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 1728 864 864, g32p_row02_traceSegment_081_1728_0864, g32p_row02_traceSegment_081_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_081_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_081 0 3456 = [8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_081 0 1728 1728, g32p_row02_traceSegment_081_0000_1728, g32p_row02_traceSegment_081_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_081 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 81 = [8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_081_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem g32p_row02_tracePolynomial_074 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 74) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 74) (g32p_literalTraceValue 1 74)
      [1, -1, 1] [-10368] = true := by
  rw [g32p_row02_traceCoefficients_074]
  decide +kernel

theorem g32p_row02_tracePolynomial_075 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 75) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 75) (g32p_literalTraceValue 1 75)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_075]
  decide +kernel

theorem g32p_row02_tracePolynomial_076 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 76) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 76) (g32p_literalTraceValue 1 76)
      [1, -1, 1] [31104, 31104, 31104] = true := by
  rw [g32p_row02_traceCoefficients_076]
  decide +kernel

theorem g32p_row02_tracePolynomial_077 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 77) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 77) (g32p_literalTraceValue 1 77)
      [1, -1, 1] [3456, 3456, 3456] = true := by
  rw [g32p_row02_traceCoefficients_077]
  decide +kernel

theorem g32p_row02_tracePolynomial_078 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 78) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 78) (g32p_literalTraceValue 1 78)
      [1, -1, 1] [10368, 10368, 10368] = true := by
  rw [g32p_row02_traceCoefficients_078]
  decide +kernel

theorem g32p_row02_tracePolynomial_079 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 79) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 79) (g32p_literalTraceValue 1 79)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_079]
  decide +kernel

theorem g32p_row02_tracePolynomial_080 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 80) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 80) (g32p_literalTraceValue 1 80)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_080]
  decide +kernel

theorem g32p_row02_tracePolynomial_081 :
    g32p_supplierTracePolynomialCheck 3456 (g32p_literalCentralizer 81) 6
      (g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 81) (g32p_literalTraceValue 1 81)
      [1, -1, 1] [] = true := by
  rw [g32p_row02_traceCoefficients_081]
  decide +kernel

end HodgeLean.Foundations.Program

end
end
