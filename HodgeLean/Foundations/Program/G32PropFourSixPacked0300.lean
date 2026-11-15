import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_041 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 41 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_041_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 13 14, g32p_row02_traceSegment_041_0000_0013, g32p_row02_traceSegment_041_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 27 13 14, g32p_row02_traceSegment_041_0027_0013, g32p_row02_traceSegment_041_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 27 27, g32p_row02_traceSegment_041_0000_0027, g32p_row02_traceSegment_041_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 54 13 14, g32p_row02_traceSegment_041_0054_0013, g32p_row02_traceSegment_041_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 81 13 14, g32p_row02_traceSegment_041_0081_0013, g32p_row02_traceSegment_041_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 54 27 27, g32p_row02_traceSegment_041_0054_0027, g32p_row02_traceSegment_041_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 54 54, g32p_row02_traceSegment_041_0000_0054, g32p_row02_traceSegment_041_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 108 13 14, g32p_row02_traceSegment_041_0108_0013, g32p_row02_traceSegment_041_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 135 13 14, g32p_row02_traceSegment_041_0135_0013, g32p_row02_traceSegment_041_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 108 27 27, g32p_row02_traceSegment_041_0108_0027, g32p_row02_traceSegment_041_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 162 13 14, g32p_row02_traceSegment_041_0162_0013, g32p_row02_traceSegment_041_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 189 13 14, g32p_row02_traceSegment_041_0189_0013, g32p_row02_traceSegment_041_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 162 27 27, g32p_row02_traceSegment_041_0162_0027, g32p_row02_traceSegment_041_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 108 54 54, g32p_row02_traceSegment_041_0108_0054, g32p_row02_traceSegment_041_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 108 108, g32p_row02_traceSegment_041_0000_0108, g32p_row02_traceSegment_041_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 216 13 14, g32p_row02_traceSegment_041_0216_0013, g32p_row02_traceSegment_041_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 243 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 243 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 243 13 14, g32p_row02_traceSegment_041_0243_0013, g32p_row02_traceSegment_041_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 216 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 216 27 27, g32p_row02_traceSegment_041_0216_0027, g32p_row02_traceSegment_041_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 270 13 14, g32p_row02_traceSegment_041_0270_0013, g32p_row02_traceSegment_041_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 297 13 14, g32p_row02_traceSegment_041_0297_0013, g32p_row02_traceSegment_041_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 270 27 27, g32p_row02_traceSegment_041_0270_0027, g32p_row02_traceSegment_041_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 216 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 216 54 54, g32p_row02_traceSegment_041_0216_0054, g32p_row02_traceSegment_041_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 337 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 324 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 324 13 14, g32p_row02_traceSegment_041_0324_0013, g32p_row02_traceSegment_041_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 351 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 364 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 351 27 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 351 13 14, g32p_row02_traceSegment_041_0351_0013, g32p_row02_traceSegment_041_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 324 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 324 27 27, g32p_row02_traceSegment_041_0324_0027, g32p_row02_traceSegment_041_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 378 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 391 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 378 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 378 13 14, g32p_row02_traceSegment_041_0378_0013, g32p_row02_traceSegment_041_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 405 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 405 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 405 13 14, g32p_row02_traceSegment_041_0405_0013, g32p_row02_traceSegment_041_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 378 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 378 27 27, g32p_row02_traceSegment_041_0378_0027, g32p_row02_traceSegment_041_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 324 108 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 324 54 54, g32p_row02_traceSegment_041_0324_0054, g32p_row02_traceSegment_041_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 216 216 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 216 108 108, g32p_row02_traceSegment_041_0216_0108, g32p_row02_traceSegment_041_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 0 432 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 216 216, g32p_row02_traceSegment_041_0000_0216, g32p_row02_traceSegment_041_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 432 13 14, g32p_row02_traceSegment_041_0432_0013, g32p_row02_traceSegment_041_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 459 13 14, g32p_row02_traceSegment_041_0459_0013, g32p_row02_traceSegment_041_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 432 27 27, g32p_row02_traceSegment_041_0432_0027, g32p_row02_traceSegment_041_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 486 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 499 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 486 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 486 13 14, g32p_row02_traceSegment_041_0486_0013, g32p_row02_traceSegment_041_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 526 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 513 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 513 13 14, g32p_row02_traceSegment_041_0513_0013, g32p_row02_traceSegment_041_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 486 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 486 27 27, g32p_row02_traceSegment_041_0486_0027, g32p_row02_traceSegment_041_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 432 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 432 54 54, g32p_row02_traceSegment_041_0432_0054, g32p_row02_traceSegment_041_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 540 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 553 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 540 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 540 13 14, g32p_row02_traceSegment_041_0540_0013, g32p_row02_traceSegment_041_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 567 13 14, g32p_row02_traceSegment_041_0567_0013, g32p_row02_traceSegment_041_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 540 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 540 27 27, g32p_row02_traceSegment_041_0540_0027, g32p_row02_traceSegment_041_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 594 13 14, g32p_row02_traceSegment_041_0594_0013, g32p_row02_traceSegment_041_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 621 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 621 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 621 13 14, g32p_row02_traceSegment_041_0621_0013, g32p_row02_traceSegment_041_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 594 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 594 27 27, g32p_row02_traceSegment_041_0594_0027, g32p_row02_traceSegment_041_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 540 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 540 54 54, g32p_row02_traceSegment_041_0540_0054, g32p_row02_traceSegment_041_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 432 216 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 432 108 108, g32p_row02_traceSegment_041_0432_0108, g32p_row02_traceSegment_041_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 648 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 661 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 648 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 648 13 14, g32p_row02_traceSegment_041_0648_0013, g32p_row02_traceSegment_041_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 688 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 675 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 675 13 14, g32p_row02_traceSegment_041_0675_0013, g32p_row02_traceSegment_041_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 648 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 648 27 27, g32p_row02_traceSegment_041_0648_0027, g32p_row02_traceSegment_041_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 702 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 702 13 14, g32p_row02_traceSegment_041_0702_0013, g32p_row02_traceSegment_041_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 729 13 14, g32p_row02_traceSegment_041_0729_0013, g32p_row02_traceSegment_041_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 702 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 702 27 27, g32p_row02_traceSegment_041_0702_0027, g32p_row02_traceSegment_041_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 648 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 648 54 54, g32p_row02_traceSegment_041_0648_0054, g32p_row02_traceSegment_041_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 756 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 769 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 756 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 756 13 14, g32p_row02_traceSegment_041_0756_0013, g32p_row02_traceSegment_041_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 796 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 783 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 783 13 14, g32p_row02_traceSegment_041_0783_0013, g32p_row02_traceSegment_041_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 756 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 756 27 27, g32p_row02_traceSegment_041_0756_0027, g32p_row02_traceSegment_041_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 810 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 810 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 810 13 14, g32p_row02_traceSegment_041_0810_0013, g32p_row02_traceSegment_041_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 850 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 837 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 837 13 14, g32p_row02_traceSegment_041_0837_0013, g32p_row02_traceSegment_041_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 810 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 810 27 27, g32p_row02_traceSegment_041_0810_0027, g32p_row02_traceSegment_041_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 756 108 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 756 54 54, g32p_row02_traceSegment_041_0756_0054, g32p_row02_traceSegment_041_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 648 216 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 648 108 108, g32p_row02_traceSegment_041_0648_0108, g32p_row02_traceSegment_041_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 432 432 = [0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 432 216 216, g32p_row02_traceSegment_041_0432_0216, g32p_row02_traceSegment_041_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_041 0 864 = [0, 0, 0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 432 432, g32p_row02_traceSegment_041_0000_0432, g32p_row02_traceSegment_041_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 877 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 864 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 864 13 14, g32p_row02_traceSegment_041_0864_0013, g32p_row02_traceSegment_041_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 891 13 = [0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 891 27 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 891 13 14, g32p_row02_traceSegment_041_0891_0013, g32p_row02_traceSegment_041_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 864 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 864 27 27, g32p_row02_traceSegment_041_0864_0027, g32p_row02_traceSegment_041_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 918 13 14, g32p_row02_traceSegment_041_0918_0013, g32p_row02_traceSegment_041_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 945 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 958 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 945 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 945 13 14, g32p_row02_traceSegment_041_0945_0013, g32p_row02_traceSegment_041_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 918 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 918 27 27, g32p_row02_traceSegment_041_0918_0027, g32p_row02_traceSegment_041_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 864 108 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 864 54 54, g32p_row02_traceSegment_041_0864_0054, g32p_row02_traceSegment_041_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 972 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 985 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 972 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 972 13 14, g32p_row02_traceSegment_041_0972_0013, g32p_row02_traceSegment_041_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 999 13 14, g32p_row02_traceSegment_041_0999_0013, g32p_row02_traceSegment_041_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 972 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 972 27 27, g32p_row02_traceSegment_041_0972_0027, g32p_row02_traceSegment_041_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1026 13 14, g32p_row02_traceSegment_041_1026_0013, g32p_row02_traceSegment_041_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1053 13 14, g32p_row02_traceSegment_041_1053_0013, g32p_row02_traceSegment_041_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1026 27 27, g32p_row02_traceSegment_041_1026_0027, g32p_row02_traceSegment_041_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 972 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 972 54 54, g32p_row02_traceSegment_041_0972_0054, g32p_row02_traceSegment_041_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 864 216 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 864 108 108, g32p_row02_traceSegment_041_0864_0108, g32p_row02_traceSegment_041_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1080 13 14, g32p_row02_traceSegment_041_1080_0013, g32p_row02_traceSegment_041_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1107 13 14, g32p_row02_traceSegment_041_1107_0013, g32p_row02_traceSegment_041_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1080 27 27, g32p_row02_traceSegment_041_1080_0027, g32p_row02_traceSegment_041_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1134 13 14, g32p_row02_traceSegment_041_1134_0013, g32p_row02_traceSegment_041_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1161 13 14, g32p_row02_traceSegment_041_1161_0013, g32p_row02_traceSegment_041_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1134 27 27, g32p_row02_traceSegment_041_1134_0027, g32p_row02_traceSegment_041_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1080 54 54, g32p_row02_traceSegment_041_1080_0054, g32p_row02_traceSegment_041_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1188 13 14, g32p_row02_traceSegment_041_1188_0013, g32p_row02_traceSegment_041_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1215 13 14, g32p_row02_traceSegment_041_1215_0013, g32p_row02_traceSegment_041_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1188 27 27, g32p_row02_traceSegment_041_1188_0027, g32p_row02_traceSegment_041_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1242 13 14, g32p_row02_traceSegment_041_1242_0013, g32p_row02_traceSegment_041_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1269 13 14, g32p_row02_traceSegment_041_1269_0013, g32p_row02_traceSegment_041_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1242 27 27, g32p_row02_traceSegment_041_1242_0027, g32p_row02_traceSegment_041_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1188 54 54, g32p_row02_traceSegment_041_1188_0054, g32p_row02_traceSegment_041_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1080 108 108, g32p_row02_traceSegment_041_1080_0108, g32p_row02_traceSegment_041_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 864 432 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 864 216 216, g32p_row02_traceSegment_041_0864_0216, g32p_row02_traceSegment_041_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1296 13 14, g32p_row02_traceSegment_041_1296_0013, g32p_row02_traceSegment_041_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1336 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1323 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1323 13 14, g32p_row02_traceSegment_041_1323_0013, g32p_row02_traceSegment_041_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1296 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1296 27 27, g32p_row02_traceSegment_041_1296_0027, g32p_row02_traceSegment_041_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1350 13 14, g32p_row02_traceSegment_041_1350_0013, g32p_row02_traceSegment_041_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1377 13 14, g32p_row02_traceSegment_041_1377_0013, g32p_row02_traceSegment_041_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1350 27 27, g32p_row02_traceSegment_041_1350_0027, g32p_row02_traceSegment_041_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1296 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1296 54 54, g32p_row02_traceSegment_041_1296_0054, g32p_row02_traceSegment_041_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1404 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1404 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1404 13 14, g32p_row02_traceSegment_041_1404_0013, g32p_row02_traceSegment_041_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1431 13 14, g32p_row02_traceSegment_041_1431_0013, g32p_row02_traceSegment_041_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1404 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1404 27 27, g32p_row02_traceSegment_041_1404_0027, g32p_row02_traceSegment_041_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1458 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1458 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1458 13 14, g32p_row02_traceSegment_041_1458_0013, g32p_row02_traceSegment_041_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1485 13 14, g32p_row02_traceSegment_041_1485_0013, g32p_row02_traceSegment_041_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1458 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1458 27 27, g32p_row02_traceSegment_041_1458_0027, g32p_row02_traceSegment_041_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1404 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1404 54 54, g32p_row02_traceSegment_041_1404_0054, g32p_row02_traceSegment_041_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 1296 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1296 108 108, g32p_row02_traceSegment_041_1296_0108, g32p_row02_traceSegment_041_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1512 13 14, g32p_row02_traceSegment_041_1512_0013, g32p_row02_traceSegment_041_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1539 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1552 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1539 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1539 13 14, g32p_row02_traceSegment_041_1539_0013, g32p_row02_traceSegment_041_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1512 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1512 27 27, g32p_row02_traceSegment_041_1512_0027, g32p_row02_traceSegment_041_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1566 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1566 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1566 13 14, g32p_row02_traceSegment_041_1566_0013, g32p_row02_traceSegment_041_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1606 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1593 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1593 13 14, g32p_row02_traceSegment_041_1593_0013, g32p_row02_traceSegment_041_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1566 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1566 27 27, g32p_row02_traceSegment_041_1566_0027, g32p_row02_traceSegment_041_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1512 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1512 54 54, g32p_row02_traceSegment_041_1512_0054, g32p_row02_traceSegment_041_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1633 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1620 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1620 13 14, g32p_row02_traceSegment_041_1620_0013, g32p_row02_traceSegment_041_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1647 13 14, g32p_row02_traceSegment_041_1647_0013, g32p_row02_traceSegment_041_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1620 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1620 27 27, g32p_row02_traceSegment_041_1620_0027, g32p_row02_traceSegment_041_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1687 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1674 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1674 13 14, g32p_row02_traceSegment_041_1674_0013, g32p_row02_traceSegment_041_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1701 13 14, g32p_row02_traceSegment_041_1701_0013, g32p_row02_traceSegment_041_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1674 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1674 27 27, g32p_row02_traceSegment_041_1674_0027, g32p_row02_traceSegment_041_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1620 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1620 54 54, g32p_row02_traceSegment_041_1620_0054, g32p_row02_traceSegment_041_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 1512 216 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1512 108 108, g32p_row02_traceSegment_041_1512_0108, g32p_row02_traceSegment_041_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 1296 432 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1296 216 216, g32p_row02_traceSegment_041_1296_0216, g32p_row02_traceSegment_041_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_041 864 864 = [0, 0, 0, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 864 432 432, g32p_row02_traceSegment_041_0864_0432, g32p_row02_traceSegment_041_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_041 0 1728 = [0, 0, 0, 0, 45] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 864 864, g32p_row02_traceSegment_041_0000_0864, g32p_row02_traceSegment_041_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1728 13 14, g32p_row02_traceSegment_041_1728_0013, g32p_row02_traceSegment_041_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1755 13 14, g32p_row02_traceSegment_041_1755_0013, g32p_row02_traceSegment_041_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1728 27 27, g32p_row02_traceSegment_041_1728_0027, g32p_row02_traceSegment_041_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1782 13 14, g32p_row02_traceSegment_041_1782_0013, g32p_row02_traceSegment_041_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1809 13 14, g32p_row02_traceSegment_041_1809_0013, g32p_row02_traceSegment_041_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1782 27 27, g32p_row02_traceSegment_041_1782_0027, g32p_row02_traceSegment_041_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1728 54 54, g32p_row02_traceSegment_041_1728_0054, g32p_row02_traceSegment_041_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1836 13 14, g32p_row02_traceSegment_041_1836_0013, g32p_row02_traceSegment_041_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1863 13 14, g32p_row02_traceSegment_041_1863_0013, g32p_row02_traceSegment_041_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1836 27 27, g32p_row02_traceSegment_041_1836_0027, g32p_row02_traceSegment_041_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1890 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1890 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1890 13 14, g32p_row02_traceSegment_041_1890_0013, g32p_row02_traceSegment_041_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1917 13 14, g32p_row02_traceSegment_041_1917_0013, g32p_row02_traceSegment_041_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1890 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1890 27 27, g32p_row02_traceSegment_041_1890_0027, g32p_row02_traceSegment_041_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1836 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1836 54 54, g32p_row02_traceSegment_041_1836_0054, g32p_row02_traceSegment_041_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1728 108 108, g32p_row02_traceSegment_041_1728_0108, g32p_row02_traceSegment_041_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1944 13 14, g32p_row02_traceSegment_041_1944_0013, g32p_row02_traceSegment_041_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1971 13 14, g32p_row02_traceSegment_041_1971_0013, g32p_row02_traceSegment_041_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1944 27 27, g32p_row02_traceSegment_041_1944_0027, g32p_row02_traceSegment_041_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1998 13 14, g32p_row02_traceSegment_041_1998_0013, g32p_row02_traceSegment_041_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2025 13 14, g32p_row02_traceSegment_041_2025_0013, g32p_row02_traceSegment_041_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1998 27 27, g32p_row02_traceSegment_041_1998_0027, g32p_row02_traceSegment_041_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1944 54 54, g32p_row02_traceSegment_041_1944_0054, g32p_row02_traceSegment_041_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2052 13 14, g32p_row02_traceSegment_041_2052_0013, g32p_row02_traceSegment_041_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2079 13 14, g32p_row02_traceSegment_041_2079_0013, g32p_row02_traceSegment_041_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2052 27 27, g32p_row02_traceSegment_041_2052_0027, g32p_row02_traceSegment_041_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2106 13 14, g32p_row02_traceSegment_041_2106_0013, g32p_row02_traceSegment_041_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2133 13 14, g32p_row02_traceSegment_041_2133_0013, g32p_row02_traceSegment_041_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2106 27 27, g32p_row02_traceSegment_041_2106_0027, g32p_row02_traceSegment_041_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2052 54 54, g32p_row02_traceSegment_041_2052_0054, g32p_row02_traceSegment_041_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1944 108 108, g32p_row02_traceSegment_041_1944_0108, g32p_row02_traceSegment_041_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1728 216 216, g32p_row02_traceSegment_041_1728_0216, g32p_row02_traceSegment_041_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2160 13 14, g32p_row02_traceSegment_041_2160_0013, g32p_row02_traceSegment_041_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2187 13 14, g32p_row02_traceSegment_041_2187_0013, g32p_row02_traceSegment_041_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2160 27 27, g32p_row02_traceSegment_041_2160_0027, g32p_row02_traceSegment_041_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2214 13 14, g32p_row02_traceSegment_041_2214_0013, g32p_row02_traceSegment_041_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2241 13 14, g32p_row02_traceSegment_041_2241_0013, g32p_row02_traceSegment_041_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2214 27 27, g32p_row02_traceSegment_041_2214_0027, g32p_row02_traceSegment_041_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2160 54 54, g32p_row02_traceSegment_041_2160_0054, g32p_row02_traceSegment_041_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2268 13 14, g32p_row02_traceSegment_041_2268_0013, g32p_row02_traceSegment_041_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2295 13 14, g32p_row02_traceSegment_041_2295_0013, g32p_row02_traceSegment_041_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2268 27 27, g32p_row02_traceSegment_041_2268_0027, g32p_row02_traceSegment_041_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2322 13 14, g32p_row02_traceSegment_041_2322_0013, g32p_row02_traceSegment_041_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2349 13 14, g32p_row02_traceSegment_041_2349_0013, g32p_row02_traceSegment_041_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2322 27 27, g32p_row02_traceSegment_041_2322_0027, g32p_row02_traceSegment_041_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2268 54 54, g32p_row02_traceSegment_041_2268_0054, g32p_row02_traceSegment_041_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2160 108 108, g32p_row02_traceSegment_041_2160_0108, g32p_row02_traceSegment_041_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2376 13 14, g32p_row02_traceSegment_041_2376_0013, g32p_row02_traceSegment_041_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2403 13 14, g32p_row02_traceSegment_041_2403_0013, g32p_row02_traceSegment_041_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2376 27 27, g32p_row02_traceSegment_041_2376_0027, g32p_row02_traceSegment_041_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2430 13 14, g32p_row02_traceSegment_041_2430_0013, g32p_row02_traceSegment_041_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2457 13 14, g32p_row02_traceSegment_041_2457_0013, g32p_row02_traceSegment_041_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2430 27 27, g32p_row02_traceSegment_041_2430_0027, g32p_row02_traceSegment_041_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2376 54 54, g32p_row02_traceSegment_041_2376_0054, g32p_row02_traceSegment_041_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2484 13 14, g32p_row02_traceSegment_041_2484_0013, g32p_row02_traceSegment_041_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2511 13 14, g32p_row02_traceSegment_041_2511_0013, g32p_row02_traceSegment_041_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2484 27 27, g32p_row02_traceSegment_041_2484_0027, g32p_row02_traceSegment_041_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2538 13 14, g32p_row02_traceSegment_041_2538_0013, g32p_row02_traceSegment_041_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2565 13 14, g32p_row02_traceSegment_041_2565_0013, g32p_row02_traceSegment_041_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2538 27 27, g32p_row02_traceSegment_041_2538_0027, g32p_row02_traceSegment_041_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2484 54 54, g32p_row02_traceSegment_041_2484_0054, g32p_row02_traceSegment_041_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2376 108 108, g32p_row02_traceSegment_041_2376_0108, g32p_row02_traceSegment_041_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2160 216 216, g32p_row02_traceSegment_041_2160_0216, g32p_row02_traceSegment_041_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 864 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1728 432 432, g32p_row02_traceSegment_041_1728_0432, g32p_row02_traceSegment_041_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2592 13 14, g32p_row02_traceSegment_041_2592_0013, g32p_row02_traceSegment_041_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2619 13 14, g32p_row02_traceSegment_041_2619_0013, g32p_row02_traceSegment_041_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2592 27 27, g32p_row02_traceSegment_041_2592_0027, g32p_row02_traceSegment_041_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2646 13 14, g32p_row02_traceSegment_041_2646_0013, g32p_row02_traceSegment_041_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2673 13 14, g32p_row02_traceSegment_041_2673_0013, g32p_row02_traceSegment_041_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2646 27 27, g32p_row02_traceSegment_041_2646_0027, g32p_row02_traceSegment_041_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2592 54 54, g32p_row02_traceSegment_041_2592_0054, g32p_row02_traceSegment_041_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2700 13 14, g32p_row02_traceSegment_041_2700_0013, g32p_row02_traceSegment_041_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2727 13 14, g32p_row02_traceSegment_041_2727_0013, g32p_row02_traceSegment_041_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2700 27 27, g32p_row02_traceSegment_041_2700_0027, g32p_row02_traceSegment_041_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2754 13 14, g32p_row02_traceSegment_041_2754_0013, g32p_row02_traceSegment_041_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2781 13 14, g32p_row02_traceSegment_041_2781_0013, g32p_row02_traceSegment_041_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2754 27 27, g32p_row02_traceSegment_041_2754_0027, g32p_row02_traceSegment_041_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2700 54 54, g32p_row02_traceSegment_041_2700_0054, g32p_row02_traceSegment_041_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2592 108 108, g32p_row02_traceSegment_041_2592_0108, g32p_row02_traceSegment_041_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2808 13 14, g32p_row02_traceSegment_041_2808_0013, g32p_row02_traceSegment_041_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2835 13 14, g32p_row02_traceSegment_041_2835_0013, g32p_row02_traceSegment_041_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2808 27 27, g32p_row02_traceSegment_041_2808_0027, g32p_row02_traceSegment_041_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2862 13 14, g32p_row02_traceSegment_041_2862_0013, g32p_row02_traceSegment_041_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2889 13 14, g32p_row02_traceSegment_041_2889_0013, g32p_row02_traceSegment_041_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2862 27 27, g32p_row02_traceSegment_041_2862_0027, g32p_row02_traceSegment_041_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2808 54 54, g32p_row02_traceSegment_041_2808_0054, g32p_row02_traceSegment_041_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2916 13 14, g32p_row02_traceSegment_041_2916_0013, g32p_row02_traceSegment_041_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2943 13 14, g32p_row02_traceSegment_041_2943_0013, g32p_row02_traceSegment_041_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2916 27 27, g32p_row02_traceSegment_041_2916_0027, g32p_row02_traceSegment_041_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2970 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2970 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2970 13 14, g32p_row02_traceSegment_041_2970_0013, g32p_row02_traceSegment_041_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2997 13 14, g32p_row02_traceSegment_041_2997_0013, g32p_row02_traceSegment_041_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 2970 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2970 27 27, g32p_row02_traceSegment_041_2970_0027, g32p_row02_traceSegment_041_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 2916 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2916 54 54, g32p_row02_traceSegment_041_2916_0054, g32p_row02_traceSegment_041_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 2808 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2808 108 108, g32p_row02_traceSegment_041_2808_0108, g32p_row02_traceSegment_041_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 2592 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2592 216 216, g32p_row02_traceSegment_041_2592_0216, g32p_row02_traceSegment_041_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3024 13 14, g32p_row02_traceSegment_041_3024_0013, g32p_row02_traceSegment_041_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3051 13 14, g32p_row02_traceSegment_041_3051_0013, g32p_row02_traceSegment_041_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3024 27 27, g32p_row02_traceSegment_041_3024_0027, g32p_row02_traceSegment_041_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3078 13 14, g32p_row02_traceSegment_041_3078_0013, g32p_row02_traceSegment_041_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3105 13 14, g32p_row02_traceSegment_041_3105_0013, g32p_row02_traceSegment_041_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3078 27 27, g32p_row02_traceSegment_041_3078_0027, g32p_row02_traceSegment_041_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3024 54 54, g32p_row02_traceSegment_041_3024_0054, g32p_row02_traceSegment_041_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3132 13 14, g32p_row02_traceSegment_041_3132_0013, g32p_row02_traceSegment_041_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3159 13 14, g32p_row02_traceSegment_041_3159_0013, g32p_row02_traceSegment_041_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3132 27 27, g32p_row02_traceSegment_041_3132_0027, g32p_row02_traceSegment_041_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3186 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3186 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3186 13 14, g32p_row02_traceSegment_041_3186_0013, g32p_row02_traceSegment_041_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3213 13 14, g32p_row02_traceSegment_041_3213_0013, g32p_row02_traceSegment_041_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3186 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3186 27 27, g32p_row02_traceSegment_041_3186_0027, g32p_row02_traceSegment_041_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 3132 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3132 54 54, g32p_row02_traceSegment_041_3132_0054, g32p_row02_traceSegment_041_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 3024 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3024 108 108, g32p_row02_traceSegment_041_3024_0108, g32p_row02_traceSegment_041_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3240 13 14, g32p_row02_traceSegment_041_3240_0013, g32p_row02_traceSegment_041_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3267 13 14, g32p_row02_traceSegment_041_3267_0013, g32p_row02_traceSegment_041_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3240 27 27, g32p_row02_traceSegment_041_3240_0027, g32p_row02_traceSegment_041_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3294 13 14, g32p_row02_traceSegment_041_3294_0013, g32p_row02_traceSegment_041_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3321 13 14, g32p_row02_traceSegment_041_3321_0013, g32p_row02_traceSegment_041_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3294 27 27, g32p_row02_traceSegment_041_3294_0027, g32p_row02_traceSegment_041_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3240 54 54, g32p_row02_traceSegment_041_3240_0054, g32p_row02_traceSegment_041_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3348 13 14, g32p_row02_traceSegment_041_3348_0013, g32p_row02_traceSegment_041_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3375 13 14, g32p_row02_traceSegment_041_3375_0013, g32p_row02_traceSegment_041_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3348 27 27, g32p_row02_traceSegment_041_3348_0027, g32p_row02_traceSegment_041_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3402 13 14, g32p_row02_traceSegment_041_3402_0013, g32p_row02_traceSegment_041_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_041 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_041 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_041_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_041 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3429 13 14, g32p_row02_traceSegment_041_3429_0013, g32p_row02_traceSegment_041_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_041 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3402 27 27, g32p_row02_traceSegment_041_3402_0027, g32p_row02_traceSegment_041_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_041 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3348 54 54, g32p_row02_traceSegment_041_3348_0054, g32p_row02_traceSegment_041_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_041 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3240 108 108, g32p_row02_traceSegment_041_3240_0108, g32p_row02_traceSegment_041_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_041_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_041 3024 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 3024 216 216, g32p_row02_traceSegment_041_3024_0216, g32p_row02_traceSegment_041_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_041_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_041 2592 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 2592 432 432, g32p_row02_traceSegment_041_2592_0432, g32p_row02_traceSegment_041_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_041_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_041 1728 1728 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 1728 864 864, g32p_row02_traceSegment_041_1728_0864, g32p_row02_traceSegment_041_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_041_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_041 0 3456 = [0, 0, 0, 0, 48] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_041 0 1728 1728, g32p_row02_traceSegment_041_0000_1728, g32p_row02_traceSegment_041_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_041 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 41 = [0, 0, 0, 0, 48] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_041_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_043 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 43 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_043_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 13 14, g32p_row02_traceSegment_043_0000_0013, g32p_row02_traceSegment_043_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 40 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 27 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 27 13 14, g32p_row02_traceSegment_043_0027_0013, g32p_row02_traceSegment_043_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 0 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 27 27, g32p_row02_traceSegment_043_0000_0027, g32p_row02_traceSegment_043_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 54 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 54 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 54 13 14, g32p_row02_traceSegment_043_0054_0013, g32p_row02_traceSegment_043_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 94 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 81 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 81 13 14, g32p_row02_traceSegment_043_0081_0013, g32p_row02_traceSegment_043_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 54 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 54 27 27, g32p_row02_traceSegment_043_0054_0027, g32p_row02_traceSegment_043_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 0 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 54 54, g32p_row02_traceSegment_043_0000_0054, g32p_row02_traceSegment_043_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 108 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 108 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 108 13 14, g32p_row02_traceSegment_043_0108_0013, g32p_row02_traceSegment_043_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 148 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 135 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 135 13 14, g32p_row02_traceSegment_043_0135_0013, g32p_row02_traceSegment_043_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 108 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 108 27 27, g32p_row02_traceSegment_043_0108_0027, g32p_row02_traceSegment_043_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 162 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 175 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 162 27 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 162 13 14, g32p_row02_traceSegment_043_0162_0013, g32p_row02_traceSegment_043_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 202 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 189 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 189 13 14, g32p_row02_traceSegment_043_0189_0013, g32p_row02_traceSegment_043_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 162 54 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 162 27 27, g32p_row02_traceSegment_043_0162_0027, g32p_row02_traceSegment_043_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 108 108 = [0, 0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 108 54 54, g32p_row02_traceSegment_043_0108_0054, g32p_row02_traceSegment_043_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 0 216 = [0, 0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 108 108, g32p_row02_traceSegment_043_0000_0108, g32p_row02_traceSegment_043_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 216 13 = [0, 0, 0, 0, 1, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 229 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 216 27 = [0, 0, 0, 0, 1, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 216 13 14, g32p_row02_traceSegment_043_0216_0013, g32p_row02_traceSegment_043_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 256 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 243 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 243 13 14, g32p_row02_traceSegment_043_0243_0013, g32p_row02_traceSegment_043_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 216 54 = [0, 0, 0, 0, 1, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 216 27 27, g32p_row02_traceSegment_043_0216_0027, g32p_row02_traceSegment_043_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 270 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 283 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 270 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 270 13 14, g32p_row02_traceSegment_043_0270_0013, g32p_row02_traceSegment_043_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 297 13 14, g32p_row02_traceSegment_043_0297_0013, g32p_row02_traceSegment_043_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 270 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 270 27 27, g32p_row02_traceSegment_043_0270_0027, g32p_row02_traceSegment_043_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 216 108 = [0, 0, 0, 0, 3, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 216 54 54, g32p_row02_traceSegment_043_0216_0054, g32p_row02_traceSegment_043_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 324 13 14, g32p_row02_traceSegment_043_0324_0013, g32p_row02_traceSegment_043_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 351 13 14, g32p_row02_traceSegment_043_0351_0013, g32p_row02_traceSegment_043_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 324 27 27, g32p_row02_traceSegment_043_0324_0027, g32p_row02_traceSegment_043_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 378 13 14, g32p_row02_traceSegment_043_0378_0013, g32p_row02_traceSegment_043_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 405 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 405 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 405 13 14, g32p_row02_traceSegment_043_0405_0013, g32p_row02_traceSegment_043_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 378 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 378 27 27, g32p_row02_traceSegment_043_0378_0027, g32p_row02_traceSegment_043_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 324 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 324 54 54, g32p_row02_traceSegment_043_0324_0054, g32p_row02_traceSegment_043_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 216 216 = [0, 0, 0, 0, 3, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 216 108 108, g32p_row02_traceSegment_043_0216_0108, g32p_row02_traceSegment_043_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 0 432 = [0, 0, 0, 0, 3, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 216 216, g32p_row02_traceSegment_043_0000_0216, g32p_row02_traceSegment_043_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 432 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 432 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 432 13 14, g32p_row02_traceSegment_043_0432_0013, g32p_row02_traceSegment_043_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 459 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 472 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 459 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 459 13 14, g32p_row02_traceSegment_043_0459_0013, g32p_row02_traceSegment_043_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 432 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 432 27 27, g32p_row02_traceSegment_043_0432_0027, g32p_row02_traceSegment_043_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 486 13 14, g32p_row02_traceSegment_043_0486_0013, g32p_row02_traceSegment_043_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 526 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 513 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 513 13 14, g32p_row02_traceSegment_043_0513_0013, g32p_row02_traceSegment_043_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 486 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 486 27 27, g32p_row02_traceSegment_043_0486_0027, g32p_row02_traceSegment_043_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 432 108 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 432 54 54, g32p_row02_traceSegment_043_0432_0054, g32p_row02_traceSegment_043_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 540 13 14, g32p_row02_traceSegment_043_0540_0013, g32p_row02_traceSegment_043_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 567 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 580 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 567 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 567 13 14, g32p_row02_traceSegment_043_0567_0013, g32p_row02_traceSegment_043_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 540 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 540 27 27, g32p_row02_traceSegment_043_0540_0027, g32p_row02_traceSegment_043_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 594 13 14, g32p_row02_traceSegment_043_0594_0013, g32p_row02_traceSegment_043_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 621 13 14, g32p_row02_traceSegment_043_0621_0013, g32p_row02_traceSegment_043_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 594 27 27, g32p_row02_traceSegment_043_0594_0027, g32p_row02_traceSegment_043_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 540 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 540 54 54, g32p_row02_traceSegment_043_0540_0054, g32p_row02_traceSegment_043_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 432 216 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 432 108 108, g32p_row02_traceSegment_043_0432_0108, g32p_row02_traceSegment_043_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 648 13 14, g32p_row02_traceSegment_043_0648_0013, g32p_row02_traceSegment_043_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 675 13 14, g32p_row02_traceSegment_043_0675_0013, g32p_row02_traceSegment_043_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 648 27 27, g32p_row02_traceSegment_043_0648_0027, g32p_row02_traceSegment_043_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 702 13 14, g32p_row02_traceSegment_043_0702_0013, g32p_row02_traceSegment_043_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 729 13 14, g32p_row02_traceSegment_043_0729_0013, g32p_row02_traceSegment_043_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 702 27 27, g32p_row02_traceSegment_043_0702_0027, g32p_row02_traceSegment_043_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 648 54 54, g32p_row02_traceSegment_043_0648_0054, g32p_row02_traceSegment_043_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 756 13 14, g32p_row02_traceSegment_043_0756_0013, g32p_row02_traceSegment_043_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 783 13 14, g32p_row02_traceSegment_043_0783_0013, g32p_row02_traceSegment_043_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 756 27 27, g32p_row02_traceSegment_043_0756_0027, g32p_row02_traceSegment_043_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 810 13 14, g32p_row02_traceSegment_043_0810_0013, g32p_row02_traceSegment_043_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 837 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 850 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 837 27 = [0, 0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 837 13 14, g32p_row02_traceSegment_043_0837_0013, g32p_row02_traceSegment_043_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 810 54 = [0, 0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 810 27 27, g32p_row02_traceSegment_043_0810_0027, g32p_row02_traceSegment_043_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 756 108 = [0, 0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 756 54 54, g32p_row02_traceSegment_043_0756_0054, g32p_row02_traceSegment_043_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 648 216 = [0, 0, 0, 0, 1, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 648 108 108, g32p_row02_traceSegment_043_0648_0108, g32p_row02_traceSegment_043_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 432 432 = [0, 0, 0, 0, 1, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 432 216 216, g32p_row02_traceSegment_043_0432_0216, g32p_row02_traceSegment_043_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_043 0 864 = [0, 0, 0, 0, 4, 36] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 432 432, g32p_row02_traceSegment_043_0000_0432, g32p_row02_traceSegment_043_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 877 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 864 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 864 13 14, g32p_row02_traceSegment_043_0864_0013, g32p_row02_traceSegment_043_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 891 13 14, g32p_row02_traceSegment_043_0891_0013, g32p_row02_traceSegment_043_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 864 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 864 27 27, g32p_row02_traceSegment_043_0864_0027, g32p_row02_traceSegment_043_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 918 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 918 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 918 13 14, g32p_row02_traceSegment_043_0918_0013, g32p_row02_traceSegment_043_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 945 13 14, g32p_row02_traceSegment_043_0945_0013, g32p_row02_traceSegment_043_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 918 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 918 27 27, g32p_row02_traceSegment_043_0918_0027, g32p_row02_traceSegment_043_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 864 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 864 54 54, g32p_row02_traceSegment_043_0864_0054, g32p_row02_traceSegment_043_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 972 13 14, g32p_row02_traceSegment_043_0972_0013, g32p_row02_traceSegment_043_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 999 13 14, g32p_row02_traceSegment_043_0999_0013, g32p_row02_traceSegment_043_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 972 27 27, g32p_row02_traceSegment_043_0972_0027, g32p_row02_traceSegment_043_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1026 13 14, g32p_row02_traceSegment_043_1026_0013, g32p_row02_traceSegment_043_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1053 13 14, g32p_row02_traceSegment_043_1053_0013, g32p_row02_traceSegment_043_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1026 27 27, g32p_row02_traceSegment_043_1026_0027, g32p_row02_traceSegment_043_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 972 54 54, g32p_row02_traceSegment_043_0972_0054, g32p_row02_traceSegment_043_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 864 216 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 864 108 108, g32p_row02_traceSegment_043_0864_0108, g32p_row02_traceSegment_043_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1080 13 14, g32p_row02_traceSegment_043_1080_0013, g32p_row02_traceSegment_043_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1107 13 14, g32p_row02_traceSegment_043_1107_0013, g32p_row02_traceSegment_043_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1080 27 27, g32p_row02_traceSegment_043_1080_0027, g32p_row02_traceSegment_043_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1147 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1134 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1134 13 14, g32p_row02_traceSegment_043_1134_0013, g32p_row02_traceSegment_043_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1161 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1174 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1161 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1161 13 14, g32p_row02_traceSegment_043_1161_0013, g32p_row02_traceSegment_043_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1134 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1134 27 27, g32p_row02_traceSegment_043_1134_0027, g32p_row02_traceSegment_043_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1080 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1080 54 54, g32p_row02_traceSegment_043_1080_0054, g32p_row02_traceSegment_043_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1188 13 14, g32p_row02_traceSegment_043_1188_0013, g32p_row02_traceSegment_043_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1215 13 14, g32p_row02_traceSegment_043_1215_0013, g32p_row02_traceSegment_043_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1188 27 27, g32p_row02_traceSegment_043_1188_0027, g32p_row02_traceSegment_043_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1242 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1255 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1242 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1242 13 14, g32p_row02_traceSegment_043_1242_0013, g32p_row02_traceSegment_043_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1282 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1269 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1269 13 14, g32p_row02_traceSegment_043_1269_0013, g32p_row02_traceSegment_043_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1242 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1242 27 27, g32p_row02_traceSegment_043_1242_0027, g32p_row02_traceSegment_043_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1188 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1188 54 54, g32p_row02_traceSegment_043_1188_0054, g32p_row02_traceSegment_043_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 1080 216 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1080 108 108, g32p_row02_traceSegment_043_1080_0108, g32p_row02_traceSegment_043_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 864 432 = [0, 0, 0, 0, 3, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 864 216 216, g32p_row02_traceSegment_043_0864_0216, g32p_row02_traceSegment_043_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1296 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1296 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1296 13 14, g32p_row02_traceSegment_043_1296_0013, g32p_row02_traceSegment_043_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1323 13 14, g32p_row02_traceSegment_043_1323_0013, g32p_row02_traceSegment_043_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1296 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1296 27 27, g32p_row02_traceSegment_043_1296_0027, g32p_row02_traceSegment_043_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1350 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1350 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1350 13 14, g32p_row02_traceSegment_043_1350_0013, g32p_row02_traceSegment_043_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1377 13 = [0, 0, 0, 0, 1, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1390 14 = [0, 0, 0, 0, 1, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1377 27 = [0, 0, 0, 0, 2, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1377 13 14, g32p_row02_traceSegment_043_1377_0013, g32p_row02_traceSegment_043_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1350 54 = [0, 0, 0, 0, 2, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1350 27 27, g32p_row02_traceSegment_043_1350_0027, g32p_row02_traceSegment_043_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1296 108 = [0, 0, 0, 0, 2, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1296 54 54, g32p_row02_traceSegment_043_1296_0054, g32p_row02_traceSegment_043_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1404 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1417 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1404 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1404 13 14, g32p_row02_traceSegment_043_1404_0013, g32p_row02_traceSegment_043_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1431 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1431 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1431 13 14, g32p_row02_traceSegment_043_1431_0013, g32p_row02_traceSegment_043_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1404 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1404 27 27, g32p_row02_traceSegment_043_1404_0027, g32p_row02_traceSegment_043_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1458 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1458 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1458 13 14, g32p_row02_traceSegment_043_1458_0013, g32p_row02_traceSegment_043_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1485 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1485 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1485 13 14, g32p_row02_traceSegment_043_1485_0013, g32p_row02_traceSegment_043_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1458 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1458 27 27, g32p_row02_traceSegment_043_1458_0027, g32p_row02_traceSegment_043_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1404 108 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1404 54 54, g32p_row02_traceSegment_043_1404_0054, g32p_row02_traceSegment_043_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 1296 216 = [0, 0, 0, 0, 9, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1296 108 108, g32p_row02_traceSegment_043_1296_0108, g32p_row02_traceSegment_043_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1512 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1512 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1512 13 14, g32p_row02_traceSegment_043_1512_0013, g32p_row02_traceSegment_043_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1539 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1539 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1539 13 14, g32p_row02_traceSegment_043_1539_0013, g32p_row02_traceSegment_043_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1512 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1512 27 27, g32p_row02_traceSegment_043_1512_0027, g32p_row02_traceSegment_043_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1566 13 14, g32p_row02_traceSegment_043_1566_0013, g32p_row02_traceSegment_043_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1593 13 14, g32p_row02_traceSegment_043_1593_0013, g32p_row02_traceSegment_043_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1566 27 27, g32p_row02_traceSegment_043_1566_0027, g32p_row02_traceSegment_043_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1512 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1512 54 54, g32p_row02_traceSegment_043_1512_0054, g32p_row02_traceSegment_043_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1620 13 14, g32p_row02_traceSegment_043_1620_0013, g32p_row02_traceSegment_043_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1660 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1647 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1647 13 14, g32p_row02_traceSegment_043_1647_0013, g32p_row02_traceSegment_043_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1620 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1620 27 27, g32p_row02_traceSegment_043_1620_0027, g32p_row02_traceSegment_043_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1687 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1674 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1674 13 14, g32p_row02_traceSegment_043_1674_0013, g32p_row02_traceSegment_043_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1714 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1701 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1701 13 14, g32p_row02_traceSegment_043_1701_0013, g32p_row02_traceSegment_043_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1674 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1674 27 27, g32p_row02_traceSegment_043_1674_0027, g32p_row02_traceSegment_043_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1620 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1620 54 54, g32p_row02_traceSegment_043_1620_0054, g32p_row02_traceSegment_043_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 1512 216 = [0, 0, 0, 0, 3, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1512 108 108, g32p_row02_traceSegment_043_1512_0108, g32p_row02_traceSegment_043_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 1296 432 = [0, 0, 0, 0, 12, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1296 216 216, g32p_row02_traceSegment_043_1296_0216, g32p_row02_traceSegment_043_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_043 864 864 = [0, 0, 0, 0, 15, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 864 432 432, g32p_row02_traceSegment_043_0864_0432, g32p_row02_traceSegment_043_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_043 0 1728 = [0, 0, 0, 0, 19, 54] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 864 864, g32p_row02_traceSegment_043_0000_0864, g32p_row02_traceSegment_043_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1741 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1728 13 14, g32p_row02_traceSegment_043_1728_0013, g32p_row02_traceSegment_043_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1755 13 14, g32p_row02_traceSegment_043_1755_0013, g32p_row02_traceSegment_043_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1728 27 27, g32p_row02_traceSegment_043_1728_0027, g32p_row02_traceSegment_043_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1782 13 14, g32p_row02_traceSegment_043_1782_0013, g32p_row02_traceSegment_043_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1822 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1809 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1809 13 14, g32p_row02_traceSegment_043_1809_0013, g32p_row02_traceSegment_043_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1782 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1782 27 27, g32p_row02_traceSegment_043_1782_0027, g32p_row02_traceSegment_043_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 108 = [0, 0, 0, 0, 1, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1728 54 54, g32p_row02_traceSegment_043_1728_0054, g32p_row02_traceSegment_043_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1836 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1849 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1836 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1836 13 14, g32p_row02_traceSegment_043_1836_0013, g32p_row02_traceSegment_043_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1863 13 14, g32p_row02_traceSegment_043_1863_0013, g32p_row02_traceSegment_043_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1836 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1836 27 27, g32p_row02_traceSegment_043_1836_0027, g32p_row02_traceSegment_043_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1890 13 14, g32p_row02_traceSegment_043_1890_0013, g32p_row02_traceSegment_043_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1917 13 14, g32p_row02_traceSegment_043_1917_0013, g32p_row02_traceSegment_043_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1890 27 27, g32p_row02_traceSegment_043_1890_0027, g32p_row02_traceSegment_043_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1836 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1836 54 54, g32p_row02_traceSegment_043_1836_0054, g32p_row02_traceSegment_043_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 216 = [0, 0, 0, 0, 4, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1728 108 108, g32p_row02_traceSegment_043_1728_0108, g32p_row02_traceSegment_043_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1944 13 14, g32p_row02_traceSegment_043_1944_0013, g32p_row02_traceSegment_043_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 1984 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1971 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1971 13 14, g32p_row02_traceSegment_043_1971_0013, g32p_row02_traceSegment_043_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1944 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1944 27 27, g32p_row02_traceSegment_043_1944_0027, g32p_row02_traceSegment_043_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 1998 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 1998 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1998 13 14, g32p_row02_traceSegment_043_1998_0013, g32p_row02_traceSegment_043_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2025 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2025 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2025 13 14, g32p_row02_traceSegment_043_2025_0013, g32p_row02_traceSegment_043_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 1998 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1998 27 27, g32p_row02_traceSegment_043_1998_0027, g32p_row02_traceSegment_043_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 1944 108 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1944 54 54, g32p_row02_traceSegment_043_1944_0054, g32p_row02_traceSegment_043_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2052 13 14, g32p_row02_traceSegment_043_2052_0013, g32p_row02_traceSegment_043_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2079 13 14, g32p_row02_traceSegment_043_2079_0013, g32p_row02_traceSegment_043_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2052 27 27, g32p_row02_traceSegment_043_2052_0027, g32p_row02_traceSegment_043_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2106 13 14, g32p_row02_traceSegment_043_2106_0013, g32p_row02_traceSegment_043_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2133 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2146 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2133 27 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2133 13 14, g32p_row02_traceSegment_043_2133_0013, g32p_row02_traceSegment_043_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2106 54 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2106 27 27, g32p_row02_traceSegment_043_2106_0027, g32p_row02_traceSegment_043_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2052 108 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2052 54 54, g32p_row02_traceSegment_043_2052_0054, g32p_row02_traceSegment_043_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 1944 216 = [0, 0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1944 108 108, g32p_row02_traceSegment_043_1944_0108, g32p_row02_traceSegment_043_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 432 = [0, 0, 0, 0, 4, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1728 216 216, g32p_row02_traceSegment_043_1728_0216, g32p_row02_traceSegment_043_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2160 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2173 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2160 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2160 13 14, g32p_row02_traceSegment_043_2160_0013, g32p_row02_traceSegment_043_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2187 13 14, g32p_row02_traceSegment_043_2187_0013, g32p_row02_traceSegment_043_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2160 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2160 27 27, g32p_row02_traceSegment_043_2160_0027, g32p_row02_traceSegment_043_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2214 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2214 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2214 13 14, g32p_row02_traceSegment_043_2214_0013, g32p_row02_traceSegment_043_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2241 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2241 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2241 13 14, g32p_row02_traceSegment_043_2241_0013, g32p_row02_traceSegment_043_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2214 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2214 27 27, g32p_row02_traceSegment_043_2214_0027, g32p_row02_traceSegment_043_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2160 108 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2160 54 54, g32p_row02_traceSegment_043_2160_0054, g32p_row02_traceSegment_043_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2268 13 14, g32p_row02_traceSegment_043_2268_0013, g32p_row02_traceSegment_043_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2295 13 14, g32p_row02_traceSegment_043_2295_0013, g32p_row02_traceSegment_043_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2268 27 27, g32p_row02_traceSegment_043_2268_0027, g32p_row02_traceSegment_043_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2335 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2322 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2322 13 14, g32p_row02_traceSegment_043_2322_0013, g32p_row02_traceSegment_043_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2349 13 14, g32p_row02_traceSegment_043_2349_0013, g32p_row02_traceSegment_043_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2322 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2322 27 27, g32p_row02_traceSegment_043_2322_0027, g32p_row02_traceSegment_043_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2268 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2268 54 54, g32p_row02_traceSegment_043_2268_0054, g32p_row02_traceSegment_043_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 2160 216 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2160 108 108, g32p_row02_traceSegment_043_2160_0108, g32p_row02_traceSegment_043_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2376 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2389 14 = [0, 0, 0, 0, 1, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2376 27 = [0, 0, 0, 0, 2, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2376 13 14, g32p_row02_traceSegment_043_2376_0013, g32p_row02_traceSegment_043_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2416 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2403 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2403 13 14, g32p_row02_traceSegment_043_2403_0013, g32p_row02_traceSegment_043_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2376 54 = [0, 0, 0, 0, 2, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2376 27 27, g32p_row02_traceSegment_043_2376_0027, g32p_row02_traceSegment_043_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2443 14 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2430 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2430 13 14, g32p_row02_traceSegment_043_2430_0013, g32p_row02_traceSegment_043_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2457 13 14, g32p_row02_traceSegment_043_2457_0013, g32p_row02_traceSegment_043_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2430 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2430 27 27, g32p_row02_traceSegment_043_2430_0027, g32p_row02_traceSegment_043_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2376 108 = [0, 0, 0, 0, 5, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2376 54 54, g32p_row02_traceSegment_043_2376_0054, g32p_row02_traceSegment_043_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2484 13 14, g32p_row02_traceSegment_043_2484_0013, g32p_row02_traceSegment_043_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2511 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2511 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2511 13 14, g32p_row02_traceSegment_043_2511_0013, g32p_row02_traceSegment_043_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2484 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2484 27 27, g32p_row02_traceSegment_043_2484_0027, g32p_row02_traceSegment_043_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2538 13 14, g32p_row02_traceSegment_043_2538_0013, g32p_row02_traceSegment_043_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2565 13 14, g32p_row02_traceSegment_043_2565_0013, g32p_row02_traceSegment_043_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2538 27 27, g32p_row02_traceSegment_043_2538_0027, g32p_row02_traceSegment_043_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2484 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2484 54 54, g32p_row02_traceSegment_043_2484_0054, g32p_row02_traceSegment_043_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 2376 216 = [0, 0, 0, 0, 5, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2376 108 108, g32p_row02_traceSegment_043_2376_0108, g32p_row02_traceSegment_043_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 2160 432 = [0, 0, 0, 0, 5, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2160 216 216, g32p_row02_traceSegment_043_2160_0216, g32p_row02_traceSegment_043_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 864 = [0, 0, 0, 0, 9, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1728 432 432, g32p_row02_traceSegment_043_1728_0432, g32p_row02_traceSegment_043_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2592 13 14, g32p_row02_traceSegment_043_2592_0013, g32p_row02_traceSegment_043_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2619 13 14, g32p_row02_traceSegment_043_2619_0013, g32p_row02_traceSegment_043_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2592 27 27, g32p_row02_traceSegment_043_2592_0027, g32p_row02_traceSegment_043_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2646 13 14, g32p_row02_traceSegment_043_2646_0013, g32p_row02_traceSegment_043_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2673 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2673 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2673 13 14, g32p_row02_traceSegment_043_2673_0013, g32p_row02_traceSegment_043_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2646 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2646 27 27, g32p_row02_traceSegment_043_2646_0027, g32p_row02_traceSegment_043_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2592 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2592 54 54, g32p_row02_traceSegment_043_2592_0054, g32p_row02_traceSegment_043_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2700 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2713 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2700 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2700 13 14, g32p_row02_traceSegment_043_2700_0013, g32p_row02_traceSegment_043_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2740 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2727 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2727 13 14, g32p_row02_traceSegment_043_2727_0013, g32p_row02_traceSegment_043_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2700 54 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2700 27 27, g32p_row02_traceSegment_043_2700_0027, g32p_row02_traceSegment_043_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2754 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2767 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2754 27 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2754 13 14, g32p_row02_traceSegment_043_2754_0013, g32p_row02_traceSegment_043_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2781 13 14, g32p_row02_traceSegment_043_2781_0013, g32p_row02_traceSegment_043_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2754 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2754 27 27, g32p_row02_traceSegment_043_2754_0027, g32p_row02_traceSegment_043_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2700 108 = [0, 0, 0, 0, 4, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2700 54 54, g32p_row02_traceSegment_043_2700_0054, g32p_row02_traceSegment_043_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 2592 216 = [0, 0, 0, 0, 4, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2592 108 108, g32p_row02_traceSegment_043_2592_0108, g32p_row02_traceSegment_043_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2808 13 14, g32p_row02_traceSegment_043_2808_0013, g32p_row02_traceSegment_043_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2835 13 14, g32p_row02_traceSegment_043_2835_0013, g32p_row02_traceSegment_043_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2808 27 27, g32p_row02_traceSegment_043_2808_0027, g32p_row02_traceSegment_043_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2862 13 14, g32p_row02_traceSegment_043_2862_0013, g32p_row02_traceSegment_043_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2889 13 14, g32p_row02_traceSegment_043_2889_0013, g32p_row02_traceSegment_043_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2862 27 27, g32p_row02_traceSegment_043_2862_0027, g32p_row02_traceSegment_043_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2808 54 54, g32p_row02_traceSegment_043_2808_0054, g32p_row02_traceSegment_043_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2916 13 14, g32p_row02_traceSegment_043_2916_0013, g32p_row02_traceSegment_043_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2943 13 14, g32p_row02_traceSegment_043_2943_0013, g32p_row02_traceSegment_043_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2916 27 27, g32p_row02_traceSegment_043_2916_0027, g32p_row02_traceSegment_043_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2970 13 14, g32p_row02_traceSegment_043_2970_0013, g32p_row02_traceSegment_043_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2997 13 14, g32p_row02_traceSegment_043_2997_0013, g32p_row02_traceSegment_043_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2970 27 27, g32p_row02_traceSegment_043_2970_0027, g32p_row02_traceSegment_043_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2916 54 54, g32p_row02_traceSegment_043_2916_0054, g32p_row02_traceSegment_043_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2808 108 108, g32p_row02_traceSegment_043_2808_0108, g32p_row02_traceSegment_043_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 2592 432 = [0, 0, 0, 0, 4, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2592 216 216, g32p_row02_traceSegment_043_2592_0216, g32p_row02_traceSegment_043_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3024 13 14, g32p_row02_traceSegment_043_3024_0013, g32p_row02_traceSegment_043_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3051 13 14, g32p_row02_traceSegment_043_3051_0013, g32p_row02_traceSegment_043_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3024 27 27, g32p_row02_traceSegment_043_3024_0027, g32p_row02_traceSegment_043_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3078 13 14, g32p_row02_traceSegment_043_3078_0013, g32p_row02_traceSegment_043_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3105 13 14, g32p_row02_traceSegment_043_3105_0013, g32p_row02_traceSegment_043_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3078 27 27, g32p_row02_traceSegment_043_3078_0027, g32p_row02_traceSegment_043_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3024 54 54, g32p_row02_traceSegment_043_3024_0054, g32p_row02_traceSegment_043_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3132 13 14, g32p_row02_traceSegment_043_3132_0013, g32p_row02_traceSegment_043_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3159 13 14, g32p_row02_traceSegment_043_3159_0013, g32p_row02_traceSegment_043_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3132 27 27, g32p_row02_traceSegment_043_3132_0027, g32p_row02_traceSegment_043_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3186 13 14, g32p_row02_traceSegment_043_3186_0013, g32p_row02_traceSegment_043_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3213 13 14, g32p_row02_traceSegment_043_3213_0013, g32p_row02_traceSegment_043_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3186 27 27, g32p_row02_traceSegment_043_3186_0027, g32p_row02_traceSegment_043_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3132 54 54, g32p_row02_traceSegment_043_3132_0054, g32p_row02_traceSegment_043_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3024 108 108, g32p_row02_traceSegment_043_3024_0108, g32p_row02_traceSegment_043_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3240 13 14, g32p_row02_traceSegment_043_3240_0013, g32p_row02_traceSegment_043_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3267 13 14, g32p_row02_traceSegment_043_3267_0013, g32p_row02_traceSegment_043_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3240 27 27, g32p_row02_traceSegment_043_3240_0027, g32p_row02_traceSegment_043_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3307 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3294 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3294 13 14, g32p_row02_traceSegment_043_3294_0013, g32p_row02_traceSegment_043_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3321 13 14, g32p_row02_traceSegment_043_3321_0013, g32p_row02_traceSegment_043_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3294 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3294 27 27, g32p_row02_traceSegment_043_3294_0027, g32p_row02_traceSegment_043_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 3240 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3240 54 54, g32p_row02_traceSegment_043_3240_0054, g32p_row02_traceSegment_043_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3361 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3348 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3348 13 14, g32p_row02_traceSegment_043_3348_0013, g32p_row02_traceSegment_043_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3375 13 14, g32p_row02_traceSegment_043_3375_0013, g32p_row02_traceSegment_043_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3348 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3348 27 27, g32p_row02_traceSegment_043_3348_0027, g32p_row02_traceSegment_043_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3402 13 14, g32p_row02_traceSegment_043_3402_0013, g32p_row02_traceSegment_043_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_043 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_043 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_043_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_043 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3429 13 14, g32p_row02_traceSegment_043_3429_0013, g32p_row02_traceSegment_043_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_043 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3402 27 27, g32p_row02_traceSegment_043_3402_0027, g32p_row02_traceSegment_043_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_043 3348 108 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3348 54 54, g32p_row02_traceSegment_043_3348_0054, g32p_row02_traceSegment_043_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_043 3240 216 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3240 108 108, g32p_row02_traceSegment_043_3240_0108, g32p_row02_traceSegment_043_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_043_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_043 3024 432 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 3024 216 216, g32p_row02_traceSegment_043_3024_0216, g32p_row02_traceSegment_043_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_043_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_043 2592 864 = [0, 0, 0, 0, 4, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 2592 432 432, g32p_row02_traceSegment_043_2592_0432, g32p_row02_traceSegment_043_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_043_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_043 1728 1728 = [0, 0, 0, 0, 13, 42] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 1728 864 864, g32p_row02_traceSegment_043_1728_0864, g32p_row02_traceSegment_043_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_043_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_043 0 3456 = [0, 0, 0, 0, 32, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_043 0 1728 1728, g32p_row02_traceSegment_043_0000_1728, g32p_row02_traceSegment_043_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_043 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 43 = [0, 0, 0, 0, 32, 96] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_043_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_044 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 44 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_044_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 13 14, g32p_row02_traceSegment_044_0000_0013, g32p_row02_traceSegment_044_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 27 13 14, g32p_row02_traceSegment_044_0027_0013, g32p_row02_traceSegment_044_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 27 27, g32p_row02_traceSegment_044_0000_0027, g32p_row02_traceSegment_044_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 54 13 14, g32p_row02_traceSegment_044_0054_0013, g32p_row02_traceSegment_044_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 81 13 14, g32p_row02_traceSegment_044_0081_0013, g32p_row02_traceSegment_044_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 54 27 27, g32p_row02_traceSegment_044_0054_0027, g32p_row02_traceSegment_044_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 54 54, g32p_row02_traceSegment_044_0000_0054, g32p_row02_traceSegment_044_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 108 13 14, g32p_row02_traceSegment_044_0108_0013, g32p_row02_traceSegment_044_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 135 13 14, g32p_row02_traceSegment_044_0135_0013, g32p_row02_traceSegment_044_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 108 27 27, g32p_row02_traceSegment_044_0108_0027, g32p_row02_traceSegment_044_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 162 13 14, g32p_row02_traceSegment_044_0162_0013, g32p_row02_traceSegment_044_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 189 13 14, g32p_row02_traceSegment_044_0189_0013, g32p_row02_traceSegment_044_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 162 27 27, g32p_row02_traceSegment_044_0162_0027, g32p_row02_traceSegment_044_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 108 54 54, g32p_row02_traceSegment_044_0108_0054, g32p_row02_traceSegment_044_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 108 108, g32p_row02_traceSegment_044_0000_0108, g32p_row02_traceSegment_044_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 216 13 14, g32p_row02_traceSegment_044_0216_0013, g32p_row02_traceSegment_044_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 243 13 14, g32p_row02_traceSegment_044_0243_0013, g32p_row02_traceSegment_044_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 216 27 27, g32p_row02_traceSegment_044_0216_0027, g32p_row02_traceSegment_044_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 270 13 14, g32p_row02_traceSegment_044_0270_0013, g32p_row02_traceSegment_044_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 297 13 14, g32p_row02_traceSegment_044_0297_0013, g32p_row02_traceSegment_044_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 270 27 27, g32p_row02_traceSegment_044_0270_0027, g32p_row02_traceSegment_044_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 216 54 54, g32p_row02_traceSegment_044_0216_0054, g32p_row02_traceSegment_044_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 324 13 14, g32p_row02_traceSegment_044_0324_0013, g32p_row02_traceSegment_044_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 351 13 14, g32p_row02_traceSegment_044_0351_0013, g32p_row02_traceSegment_044_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 324 27 27, g32p_row02_traceSegment_044_0324_0027, g32p_row02_traceSegment_044_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 378 13 14, g32p_row02_traceSegment_044_0378_0013, g32p_row02_traceSegment_044_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 405 13 14, g32p_row02_traceSegment_044_0405_0013, g32p_row02_traceSegment_044_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 378 27 27, g32p_row02_traceSegment_044_0378_0027, g32p_row02_traceSegment_044_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 324 54 54, g32p_row02_traceSegment_044_0324_0054, g32p_row02_traceSegment_044_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 216 108 108, g32p_row02_traceSegment_044_0216_0108, g32p_row02_traceSegment_044_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 216 216, g32p_row02_traceSegment_044_0000_0216, g32p_row02_traceSegment_044_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 445 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 432 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 432 13 14, g32p_row02_traceSegment_044_0432_0013, g32p_row02_traceSegment_044_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 459 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 459 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 459 13 14, g32p_row02_traceSegment_044_0459_0013, g32p_row02_traceSegment_044_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 432 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 432 27 27, g32p_row02_traceSegment_044_0432_0027, g32p_row02_traceSegment_044_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 499 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 486 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 486 13 14, g32p_row02_traceSegment_044_0486_0013, g32p_row02_traceSegment_044_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 513 13 14, g32p_row02_traceSegment_044_0513_0013, g32p_row02_traceSegment_044_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 486 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 486 27 27, g32p_row02_traceSegment_044_0486_0027, g32p_row02_traceSegment_044_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 432 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 432 54 54, g32p_row02_traceSegment_044_0432_0054, g32p_row02_traceSegment_044_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 540 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 540 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 540 13 14, g32p_row02_traceSegment_044_0540_0013, g32p_row02_traceSegment_044_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 567 13 14, g32p_row02_traceSegment_044_0567_0013, g32p_row02_traceSegment_044_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 540 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 540 27 27, g32p_row02_traceSegment_044_0540_0027, g32p_row02_traceSegment_044_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 594 13 14, g32p_row02_traceSegment_044_0594_0013, g32p_row02_traceSegment_044_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 621 13 14, g32p_row02_traceSegment_044_0621_0013, g32p_row02_traceSegment_044_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 594 27 27, g32p_row02_traceSegment_044_0594_0027, g32p_row02_traceSegment_044_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 540 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 540 54 54, g32p_row02_traceSegment_044_0540_0054, g32p_row02_traceSegment_044_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 432 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 432 108 108, g32p_row02_traceSegment_044_0432_0108, g32p_row02_traceSegment_044_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 648 13 14, g32p_row02_traceSegment_044_0648_0013, g32p_row02_traceSegment_044_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 675 13 14, g32p_row02_traceSegment_044_0675_0013, g32p_row02_traceSegment_044_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 648 27 27, g32p_row02_traceSegment_044_0648_0027, g32p_row02_traceSegment_044_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 702 13 14, g32p_row02_traceSegment_044_0702_0013, g32p_row02_traceSegment_044_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 729 13 14, g32p_row02_traceSegment_044_0729_0013, g32p_row02_traceSegment_044_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 702 27 27, g32p_row02_traceSegment_044_0702_0027, g32p_row02_traceSegment_044_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 648 54 54, g32p_row02_traceSegment_044_0648_0054, g32p_row02_traceSegment_044_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 756 13 14, g32p_row02_traceSegment_044_0756_0013, g32p_row02_traceSegment_044_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 783 13 14, g32p_row02_traceSegment_044_0783_0013, g32p_row02_traceSegment_044_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 756 27 27, g32p_row02_traceSegment_044_0756_0027, g32p_row02_traceSegment_044_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 810 13 14, g32p_row02_traceSegment_044_0810_0013, g32p_row02_traceSegment_044_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 837 13 14, g32p_row02_traceSegment_044_0837_0013, g32p_row02_traceSegment_044_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 810 27 27, g32p_row02_traceSegment_044_0810_0027, g32p_row02_traceSegment_044_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 756 54 54, g32p_row02_traceSegment_044_0756_0054, g32p_row02_traceSegment_044_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 648 108 108, g32p_row02_traceSegment_044_0648_0108, g32p_row02_traceSegment_044_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 432 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 432 216 216, g32p_row02_traceSegment_044_0432_0216, g32p_row02_traceSegment_044_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_044 0 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 432 432, g32p_row02_traceSegment_044_0000_0432, g32p_row02_traceSegment_044_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 864 13 14, g32p_row02_traceSegment_044_0864_0013, g32p_row02_traceSegment_044_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 891 13 14, g32p_row02_traceSegment_044_0891_0013, g32p_row02_traceSegment_044_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 864 27 27, g32p_row02_traceSegment_044_0864_0027, g32p_row02_traceSegment_044_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 918 13 14, g32p_row02_traceSegment_044_0918_0013, g32p_row02_traceSegment_044_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 945 13 14, g32p_row02_traceSegment_044_0945_0013, g32p_row02_traceSegment_044_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 918 27 27, g32p_row02_traceSegment_044_0918_0027, g32p_row02_traceSegment_044_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 864 54 54, g32p_row02_traceSegment_044_0864_0054, g32p_row02_traceSegment_044_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 972 13 14, g32p_row02_traceSegment_044_0972_0013, g32p_row02_traceSegment_044_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 999 13 14, g32p_row02_traceSegment_044_0999_0013, g32p_row02_traceSegment_044_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 972 27 27, g32p_row02_traceSegment_044_0972_0027, g32p_row02_traceSegment_044_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1026 13 14, g32p_row02_traceSegment_044_1026_0013, g32p_row02_traceSegment_044_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1053 13 14, g32p_row02_traceSegment_044_1053_0013, g32p_row02_traceSegment_044_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1026 27 27, g32p_row02_traceSegment_044_1026_0027, g32p_row02_traceSegment_044_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 972 54 54, g32p_row02_traceSegment_044_0972_0054, g32p_row02_traceSegment_044_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 864 108 108, g32p_row02_traceSegment_044_0864_0108, g32p_row02_traceSegment_044_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1080 13 14, g32p_row02_traceSegment_044_1080_0013, g32p_row02_traceSegment_044_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1107 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1107 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1107 13 14, g32p_row02_traceSegment_044_1107_0013, g32p_row02_traceSegment_044_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1080 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1080 27 27, g32p_row02_traceSegment_044_1080_0027, g32p_row02_traceSegment_044_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1134 13 14, g32p_row02_traceSegment_044_1134_0013, g32p_row02_traceSegment_044_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1161 13 14, g32p_row02_traceSegment_044_1161_0013, g32p_row02_traceSegment_044_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1134 27 27, g32p_row02_traceSegment_044_1134_0027, g32p_row02_traceSegment_044_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1080 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1080 54 54, g32p_row02_traceSegment_044_1080_0054, g32p_row02_traceSegment_044_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1188 13 14, g32p_row02_traceSegment_044_1188_0013, g32p_row02_traceSegment_044_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1215 13 14, g32p_row02_traceSegment_044_1215_0013, g32p_row02_traceSegment_044_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1188 27 27, g32p_row02_traceSegment_044_1188_0027, g32p_row02_traceSegment_044_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1242 13 14, g32p_row02_traceSegment_044_1242_0013, g32p_row02_traceSegment_044_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1269 13 14, g32p_row02_traceSegment_044_1269_0013, g32p_row02_traceSegment_044_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1242 27 27, g32p_row02_traceSegment_044_1242_0027, g32p_row02_traceSegment_044_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1188 54 54, g32p_row02_traceSegment_044_1188_0054, g32p_row02_traceSegment_044_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 1080 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1080 108 108, g32p_row02_traceSegment_044_1080_0108, g32p_row02_traceSegment_044_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 864 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 864 216 216, g32p_row02_traceSegment_044_0864_0216, g32p_row02_traceSegment_044_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1296 13 14, g32p_row02_traceSegment_044_1296_0013, g32p_row02_traceSegment_044_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1323 13 14, g32p_row02_traceSegment_044_1323_0013, g32p_row02_traceSegment_044_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1296 27 27, g32p_row02_traceSegment_044_1296_0027, g32p_row02_traceSegment_044_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1350 13 14, g32p_row02_traceSegment_044_1350_0013, g32p_row02_traceSegment_044_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1377 13 14, g32p_row02_traceSegment_044_1377_0013, g32p_row02_traceSegment_044_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1350 27 27, g32p_row02_traceSegment_044_1350_0027, g32p_row02_traceSegment_044_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1296 54 54, g32p_row02_traceSegment_044_1296_0054, g32p_row02_traceSegment_044_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1404 13 14, g32p_row02_traceSegment_044_1404_0013, g32p_row02_traceSegment_044_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1431 13 14, g32p_row02_traceSegment_044_1431_0013, g32p_row02_traceSegment_044_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1404 27 27, g32p_row02_traceSegment_044_1404_0027, g32p_row02_traceSegment_044_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1471 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1458 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1458 13 14, g32p_row02_traceSegment_044_1458_0013, g32p_row02_traceSegment_044_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1485 13 14, g32p_row02_traceSegment_044_1485_0013, g32p_row02_traceSegment_044_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1458 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1458 27 27, g32p_row02_traceSegment_044_1458_0027, g32p_row02_traceSegment_044_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1404 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1404 54 54, g32p_row02_traceSegment_044_1404_0054, g32p_row02_traceSegment_044_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 1296 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1296 108 108, g32p_row02_traceSegment_044_1296_0108, g32p_row02_traceSegment_044_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1512 13 14, g32p_row02_traceSegment_044_1512_0013, g32p_row02_traceSegment_044_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1539 13 14, g32p_row02_traceSegment_044_1539_0013, g32p_row02_traceSegment_044_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1512 27 27, g32p_row02_traceSegment_044_1512_0027, g32p_row02_traceSegment_044_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1566 13 14, g32p_row02_traceSegment_044_1566_0013, g32p_row02_traceSegment_044_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1593 13 14, g32p_row02_traceSegment_044_1593_0013, g32p_row02_traceSegment_044_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1566 27 27, g32p_row02_traceSegment_044_1566_0027, g32p_row02_traceSegment_044_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1512 54 54, g32p_row02_traceSegment_044_1512_0054, g32p_row02_traceSegment_044_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1620 13 14, g32p_row02_traceSegment_044_1620_0013, g32p_row02_traceSegment_044_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1647 13 14, g32p_row02_traceSegment_044_1647_0013, g32p_row02_traceSegment_044_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1620 27 27, g32p_row02_traceSegment_044_1620_0027, g32p_row02_traceSegment_044_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1674 13 14, g32p_row02_traceSegment_044_1674_0013, g32p_row02_traceSegment_044_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1701 13 14, g32p_row02_traceSegment_044_1701_0013, g32p_row02_traceSegment_044_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1674 27 27, g32p_row02_traceSegment_044_1674_0027, g32p_row02_traceSegment_044_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1620 54 54, g32p_row02_traceSegment_044_1620_0054, g32p_row02_traceSegment_044_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1512 108 108, g32p_row02_traceSegment_044_1512_0108, g32p_row02_traceSegment_044_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 1296 432 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1296 216 216, g32p_row02_traceSegment_044_1296_0216, g32p_row02_traceSegment_044_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_044 864 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 864 432 432, g32p_row02_traceSegment_044_0864_0432, g32p_row02_traceSegment_044_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_044 0 1728 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 864 864, g32p_row02_traceSegment_044_0000_0864, g32p_row02_traceSegment_044_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1728 13 14, g32p_row02_traceSegment_044_1728_0013, g32p_row02_traceSegment_044_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1755 13 14, g32p_row02_traceSegment_044_1755_0013, g32p_row02_traceSegment_044_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1728 27 27, g32p_row02_traceSegment_044_1728_0027, g32p_row02_traceSegment_044_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1782 13 14, g32p_row02_traceSegment_044_1782_0013, g32p_row02_traceSegment_044_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1809 13 14, g32p_row02_traceSegment_044_1809_0013, g32p_row02_traceSegment_044_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1782 27 27, g32p_row02_traceSegment_044_1782_0027, g32p_row02_traceSegment_044_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1728 54 54, g32p_row02_traceSegment_044_1728_0054, g32p_row02_traceSegment_044_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1836 13 14, g32p_row02_traceSegment_044_1836_0013, g32p_row02_traceSegment_044_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1863 13 14, g32p_row02_traceSegment_044_1863_0013, g32p_row02_traceSegment_044_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1836 27 27, g32p_row02_traceSegment_044_1836_0027, g32p_row02_traceSegment_044_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1890 13 14, g32p_row02_traceSegment_044_1890_0013, g32p_row02_traceSegment_044_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1917 13 14, g32p_row02_traceSegment_044_1917_0013, g32p_row02_traceSegment_044_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1890 27 27, g32p_row02_traceSegment_044_1890_0027, g32p_row02_traceSegment_044_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1836 54 54, g32p_row02_traceSegment_044_1836_0054, g32p_row02_traceSegment_044_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1728 108 108, g32p_row02_traceSegment_044_1728_0108, g32p_row02_traceSegment_044_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1944 13 14, g32p_row02_traceSegment_044_1944_0013, g32p_row02_traceSegment_044_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1971 13 14, g32p_row02_traceSegment_044_1971_0013, g32p_row02_traceSegment_044_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1944 27 27, g32p_row02_traceSegment_044_1944_0027, g32p_row02_traceSegment_044_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1998 13 14, g32p_row02_traceSegment_044_1998_0013, g32p_row02_traceSegment_044_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2025 13 14, g32p_row02_traceSegment_044_2025_0013, g32p_row02_traceSegment_044_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1998 27 27, g32p_row02_traceSegment_044_1998_0027, g32p_row02_traceSegment_044_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1944 54 54, g32p_row02_traceSegment_044_1944_0054, g32p_row02_traceSegment_044_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2052 13 14, g32p_row02_traceSegment_044_2052_0013, g32p_row02_traceSegment_044_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2079 13 14, g32p_row02_traceSegment_044_2079_0013, g32p_row02_traceSegment_044_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2052 27 27, g32p_row02_traceSegment_044_2052_0027, g32p_row02_traceSegment_044_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2106 13 14, g32p_row02_traceSegment_044_2106_0013, g32p_row02_traceSegment_044_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2133 13 14, g32p_row02_traceSegment_044_2133_0013, g32p_row02_traceSegment_044_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2106 27 27, g32p_row02_traceSegment_044_2106_0027, g32p_row02_traceSegment_044_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2052 54 54, g32p_row02_traceSegment_044_2052_0054, g32p_row02_traceSegment_044_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1944 108 108, g32p_row02_traceSegment_044_1944_0108, g32p_row02_traceSegment_044_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1728 216 216, g32p_row02_traceSegment_044_1728_0216, g32p_row02_traceSegment_044_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2160 13 14, g32p_row02_traceSegment_044_2160_0013, g32p_row02_traceSegment_044_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2187 13 14, g32p_row02_traceSegment_044_2187_0013, g32p_row02_traceSegment_044_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2160 27 27, g32p_row02_traceSegment_044_2160_0027, g32p_row02_traceSegment_044_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2214 13 14, g32p_row02_traceSegment_044_2214_0013, g32p_row02_traceSegment_044_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2241 13 14, g32p_row02_traceSegment_044_2241_0013, g32p_row02_traceSegment_044_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2214 27 27, g32p_row02_traceSegment_044_2214_0027, g32p_row02_traceSegment_044_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2160 54 54, g32p_row02_traceSegment_044_2160_0054, g32p_row02_traceSegment_044_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2268 13 14, g32p_row02_traceSegment_044_2268_0013, g32p_row02_traceSegment_044_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2295 13 14, g32p_row02_traceSegment_044_2295_0013, g32p_row02_traceSegment_044_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2268 27 27, g32p_row02_traceSegment_044_2268_0027, g32p_row02_traceSegment_044_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2322 13 14, g32p_row02_traceSegment_044_2322_0013, g32p_row02_traceSegment_044_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2349 13 14, g32p_row02_traceSegment_044_2349_0013, g32p_row02_traceSegment_044_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2322 27 27, g32p_row02_traceSegment_044_2322_0027, g32p_row02_traceSegment_044_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2268 54 54, g32p_row02_traceSegment_044_2268_0054, g32p_row02_traceSegment_044_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2160 108 108, g32p_row02_traceSegment_044_2160_0108, g32p_row02_traceSegment_044_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2376 13 14, g32p_row02_traceSegment_044_2376_0013, g32p_row02_traceSegment_044_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2403 13 14, g32p_row02_traceSegment_044_2403_0013, g32p_row02_traceSegment_044_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2376 27 27, g32p_row02_traceSegment_044_2376_0027, g32p_row02_traceSegment_044_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2430 13 14, g32p_row02_traceSegment_044_2430_0013, g32p_row02_traceSegment_044_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2457 13 14, g32p_row02_traceSegment_044_2457_0013, g32p_row02_traceSegment_044_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2430 27 27, g32p_row02_traceSegment_044_2430_0027, g32p_row02_traceSegment_044_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2376 54 54, g32p_row02_traceSegment_044_2376_0054, g32p_row02_traceSegment_044_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2484 13 14, g32p_row02_traceSegment_044_2484_0013, g32p_row02_traceSegment_044_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2511 13 14, g32p_row02_traceSegment_044_2511_0013, g32p_row02_traceSegment_044_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2484 27 27, g32p_row02_traceSegment_044_2484_0027, g32p_row02_traceSegment_044_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2538 13 14, g32p_row02_traceSegment_044_2538_0013, g32p_row02_traceSegment_044_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2565 13 14, g32p_row02_traceSegment_044_2565_0013, g32p_row02_traceSegment_044_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2538 27 27, g32p_row02_traceSegment_044_2538_0027, g32p_row02_traceSegment_044_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2484 54 54, g32p_row02_traceSegment_044_2484_0054, g32p_row02_traceSegment_044_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2376 108 108, g32p_row02_traceSegment_044_2376_0108, g32p_row02_traceSegment_044_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2160 216 216, g32p_row02_traceSegment_044_2160_0216, g32p_row02_traceSegment_044_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1728 432 432, g32p_row02_traceSegment_044_1728_0432, g32p_row02_traceSegment_044_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2592 13 14, g32p_row02_traceSegment_044_2592_0013, g32p_row02_traceSegment_044_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2619 13 14, g32p_row02_traceSegment_044_2619_0013, g32p_row02_traceSegment_044_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2592 27 27, g32p_row02_traceSegment_044_2592_0027, g32p_row02_traceSegment_044_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2646 13 14, g32p_row02_traceSegment_044_2646_0013, g32p_row02_traceSegment_044_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2673 13 14, g32p_row02_traceSegment_044_2673_0013, g32p_row02_traceSegment_044_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2646 27 27, g32p_row02_traceSegment_044_2646_0027, g32p_row02_traceSegment_044_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2592 54 54, g32p_row02_traceSegment_044_2592_0054, g32p_row02_traceSegment_044_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2700 13 14, g32p_row02_traceSegment_044_2700_0013, g32p_row02_traceSegment_044_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2727 13 14, g32p_row02_traceSegment_044_2727_0013, g32p_row02_traceSegment_044_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2700 27 27, g32p_row02_traceSegment_044_2700_0027, g32p_row02_traceSegment_044_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2754 13 14, g32p_row02_traceSegment_044_2754_0013, g32p_row02_traceSegment_044_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2781 13 14, g32p_row02_traceSegment_044_2781_0013, g32p_row02_traceSegment_044_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2754 27 27, g32p_row02_traceSegment_044_2754_0027, g32p_row02_traceSegment_044_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2700 54 54, g32p_row02_traceSegment_044_2700_0054, g32p_row02_traceSegment_044_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2592 108 108, g32p_row02_traceSegment_044_2592_0108, g32p_row02_traceSegment_044_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2808 13 14, g32p_row02_traceSegment_044_2808_0013, g32p_row02_traceSegment_044_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2848 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2835 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2835 13 14, g32p_row02_traceSegment_044_2835_0013, g32p_row02_traceSegment_044_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2808 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2808 27 27, g32p_row02_traceSegment_044_2808_0027, g32p_row02_traceSegment_044_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2875 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2862 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2862 13 14, g32p_row02_traceSegment_044_2862_0013, g32p_row02_traceSegment_044_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2889 13 14, g32p_row02_traceSegment_044_2889_0013, g32p_row02_traceSegment_044_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2862 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2862 27 27, g32p_row02_traceSegment_044_2862_0027, g32p_row02_traceSegment_044_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2808 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2808 54 54, g32p_row02_traceSegment_044_2808_0054, g32p_row02_traceSegment_044_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2916 13 14, g32p_row02_traceSegment_044_2916_0013, g32p_row02_traceSegment_044_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2943 13 14, g32p_row02_traceSegment_044_2943_0013, g32p_row02_traceSegment_044_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2916 27 27, g32p_row02_traceSegment_044_2916_0027, g32p_row02_traceSegment_044_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2970 13 14, g32p_row02_traceSegment_044_2970_0013, g32p_row02_traceSegment_044_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2997 13 14, g32p_row02_traceSegment_044_2997_0013, g32p_row02_traceSegment_044_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2970 27 27, g32p_row02_traceSegment_044_2970_0027, g32p_row02_traceSegment_044_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2916 54 54, g32p_row02_traceSegment_044_2916_0054, g32p_row02_traceSegment_044_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 2808 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2808 108 108, g32p_row02_traceSegment_044_2808_0108, g32p_row02_traceSegment_044_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 2592 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2592 216 216, g32p_row02_traceSegment_044_2592_0216, g32p_row02_traceSegment_044_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3024 13 14, g32p_row02_traceSegment_044_3024_0013, g32p_row02_traceSegment_044_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3051 13 14, g32p_row02_traceSegment_044_3051_0013, g32p_row02_traceSegment_044_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3024 27 27, g32p_row02_traceSegment_044_3024_0027, g32p_row02_traceSegment_044_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3078 13 14, g32p_row02_traceSegment_044_3078_0013, g32p_row02_traceSegment_044_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3105 13 14, g32p_row02_traceSegment_044_3105_0013, g32p_row02_traceSegment_044_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3078 27 27, g32p_row02_traceSegment_044_3078_0027, g32p_row02_traceSegment_044_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3024 54 54, g32p_row02_traceSegment_044_3024_0054, g32p_row02_traceSegment_044_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3132 13 14, g32p_row02_traceSegment_044_3132_0013, g32p_row02_traceSegment_044_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3159 13 14, g32p_row02_traceSegment_044_3159_0013, g32p_row02_traceSegment_044_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3132 27 27, g32p_row02_traceSegment_044_3132_0027, g32p_row02_traceSegment_044_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3186 13 14, g32p_row02_traceSegment_044_3186_0013, g32p_row02_traceSegment_044_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3213 13 14, g32p_row02_traceSegment_044_3213_0013, g32p_row02_traceSegment_044_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3186 27 27, g32p_row02_traceSegment_044_3186_0027, g32p_row02_traceSegment_044_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3132 54 54, g32p_row02_traceSegment_044_3132_0054, g32p_row02_traceSegment_044_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3024 108 108, g32p_row02_traceSegment_044_3024_0108, g32p_row02_traceSegment_044_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3240 13 14, g32p_row02_traceSegment_044_3240_0013, g32p_row02_traceSegment_044_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3267 13 14, g32p_row02_traceSegment_044_3267_0013, g32p_row02_traceSegment_044_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3240 27 27, g32p_row02_traceSegment_044_3240_0027, g32p_row02_traceSegment_044_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3294 13 14, g32p_row02_traceSegment_044_3294_0013, g32p_row02_traceSegment_044_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3321 13 14, g32p_row02_traceSegment_044_3321_0013, g32p_row02_traceSegment_044_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3294 27 27, g32p_row02_traceSegment_044_3294_0027, g32p_row02_traceSegment_044_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3240 54 54, g32p_row02_traceSegment_044_3240_0054, g32p_row02_traceSegment_044_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3348 13 14, g32p_row02_traceSegment_044_3348_0013, g32p_row02_traceSegment_044_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3375 13 14, g32p_row02_traceSegment_044_3375_0013, g32p_row02_traceSegment_044_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3348 27 27, g32p_row02_traceSegment_044_3348_0027, g32p_row02_traceSegment_044_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3402 13 14, g32p_row02_traceSegment_044_3402_0013, g32p_row02_traceSegment_044_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_044 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_044 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_044_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_044 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3429 13 14, g32p_row02_traceSegment_044_3429_0013, g32p_row02_traceSegment_044_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_044 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3402 27 27, g32p_row02_traceSegment_044_3402_0027, g32p_row02_traceSegment_044_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_044 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3348 54 54, g32p_row02_traceSegment_044_3348_0054, g32p_row02_traceSegment_044_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_044 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3240 108 108, g32p_row02_traceSegment_044_3240_0108, g32p_row02_traceSegment_044_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_044_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_044 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 3024 216 216, g32p_row02_traceSegment_044_3024_0216, g32p_row02_traceSegment_044_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_044_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_044 2592 864 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 2592 432 432, g32p_row02_traceSegment_044_2592_0432, g32p_row02_traceSegment_044_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_044_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_044 1728 1728 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 1728 864 864, g32p_row02_traceSegment_044_1728_0864, g32p_row02_traceSegment_044_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_044_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_044 0 3456 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_044 0 1728 1728, g32p_row02_traceSegment_044_0000_1728, g32p_row02_traceSegment_044_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_044 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 44 = [0, 0, 0, 0, 8] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_044_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_045 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 45 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_045_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 13 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 0 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 13 14, g32p_row02_traceSegment_045_0000_0013, g32p_row02_traceSegment_045_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 27 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 27 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 27 13 14, g32p_row02_traceSegment_045_0027_0013, g32p_row02_traceSegment_045_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 0 54 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 27 27, g32p_row02_traceSegment_045_0000_0027, g32p_row02_traceSegment_045_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 54 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 67 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 54 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 54 13 14, g32p_row02_traceSegment_045_0054_0013, g32p_row02_traceSegment_045_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 81 13 14, g32p_row02_traceSegment_045_0081_0013, g32p_row02_traceSegment_045_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 54 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 54 27 27, g32p_row02_traceSegment_045_0054_0027, g32p_row02_traceSegment_045_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 0 108 = [0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 54 54, g32p_row02_traceSegment_045_0000_0054, g32p_row02_traceSegment_045_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 108 13 14, g32p_row02_traceSegment_045_0108_0013, g32p_row02_traceSegment_045_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 135 13 14, g32p_row02_traceSegment_045_0135_0013, g32p_row02_traceSegment_045_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 108 27 27, g32p_row02_traceSegment_045_0108_0027, g32p_row02_traceSegment_045_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 162 13 14, g32p_row02_traceSegment_045_0162_0013, g32p_row02_traceSegment_045_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 189 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 202 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 189 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 189 13 14, g32p_row02_traceSegment_045_0189_0013, g32p_row02_traceSegment_045_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 162 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 162 27 27, g32p_row02_traceSegment_045_0162_0027, g32p_row02_traceSegment_045_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 108 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 108 54 54, g32p_row02_traceSegment_045_0108_0054, g32p_row02_traceSegment_045_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 0 216 = [0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 108 108, g32p_row02_traceSegment_045_0000_0108, g32p_row02_traceSegment_045_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 216 13 14, g32p_row02_traceSegment_045_0216_0013, g32p_row02_traceSegment_045_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 243 13 14, g32p_row02_traceSegment_045_0243_0013, g32p_row02_traceSegment_045_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 216 27 27, g32p_row02_traceSegment_045_0216_0027, g32p_row02_traceSegment_045_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 270 13 14, g32p_row02_traceSegment_045_0270_0013, g32p_row02_traceSegment_045_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 297 13 14, g32p_row02_traceSegment_045_0297_0013, g32p_row02_traceSegment_045_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 270 27 27, g32p_row02_traceSegment_045_0270_0027, g32p_row02_traceSegment_045_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 216 54 54, g32p_row02_traceSegment_045_0216_0054, g32p_row02_traceSegment_045_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 324 13 14, g32p_row02_traceSegment_045_0324_0013, g32p_row02_traceSegment_045_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 351 13 14, g32p_row02_traceSegment_045_0351_0013, g32p_row02_traceSegment_045_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 324 27 27, g32p_row02_traceSegment_045_0324_0027, g32p_row02_traceSegment_045_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 378 13 14, g32p_row02_traceSegment_045_0378_0013, g32p_row02_traceSegment_045_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 418 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 405 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 405 13 14, g32p_row02_traceSegment_045_0405_0013, g32p_row02_traceSegment_045_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 378 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 378 27 27, g32p_row02_traceSegment_045_0378_0027, g32p_row02_traceSegment_045_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 324 108 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 324 54 54, g32p_row02_traceSegment_045_0324_0054, g32p_row02_traceSegment_045_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 216 216 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 216 108 108, g32p_row02_traceSegment_045_0216_0108, g32p_row02_traceSegment_045_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 0 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 216 216, g32p_row02_traceSegment_045_0000_0216, g32p_row02_traceSegment_045_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 432 13 14, g32p_row02_traceSegment_045_0432_0013, g32p_row02_traceSegment_045_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 459 13 14, g32p_row02_traceSegment_045_0459_0013, g32p_row02_traceSegment_045_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 432 27 27, g32p_row02_traceSegment_045_0432_0027, g32p_row02_traceSegment_045_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 486 13 14, g32p_row02_traceSegment_045_0486_0013, g32p_row02_traceSegment_045_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 513 13 14, g32p_row02_traceSegment_045_0513_0013, g32p_row02_traceSegment_045_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 486 27 27, g32p_row02_traceSegment_045_0486_0027, g32p_row02_traceSegment_045_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 432 54 54, g32p_row02_traceSegment_045_0432_0054, g32p_row02_traceSegment_045_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 540 13 14, g32p_row02_traceSegment_045_0540_0013, g32p_row02_traceSegment_045_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 567 13 14, g32p_row02_traceSegment_045_0567_0013, g32p_row02_traceSegment_045_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 540 27 27, g32p_row02_traceSegment_045_0540_0027, g32p_row02_traceSegment_045_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 594 13 14, g32p_row02_traceSegment_045_0594_0013, g32p_row02_traceSegment_045_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 621 13 14, g32p_row02_traceSegment_045_0621_0013, g32p_row02_traceSegment_045_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 594 27 27, g32p_row02_traceSegment_045_0594_0027, g32p_row02_traceSegment_045_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 540 54 54, g32p_row02_traceSegment_045_0540_0054, g32p_row02_traceSegment_045_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 432 108 108, g32p_row02_traceSegment_045_0432_0108, g32p_row02_traceSegment_045_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 648 13 14, g32p_row02_traceSegment_045_0648_0013, g32p_row02_traceSegment_045_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 675 13 14, g32p_row02_traceSegment_045_0675_0013, g32p_row02_traceSegment_045_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 648 27 27, g32p_row02_traceSegment_045_0648_0027, g32p_row02_traceSegment_045_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 702 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 702 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 702 13 14, g32p_row02_traceSegment_045_0702_0013, g32p_row02_traceSegment_045_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 729 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 742 14 = [0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 729 27 = [0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 729 13 14, g32p_row02_traceSegment_045_0729_0013, g32p_row02_traceSegment_045_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 702 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 702 27 27, g32p_row02_traceSegment_045_0702_0027, g32p_row02_traceSegment_045_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 648 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 648 54 54, g32p_row02_traceSegment_045_0648_0054, g32p_row02_traceSegment_045_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 756 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 769 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 756 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 756 13 14, g32p_row02_traceSegment_045_0756_0013, g32p_row02_traceSegment_045_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 783 13 14, g32p_row02_traceSegment_045_0783_0013, g32p_row02_traceSegment_045_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 756 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 756 27 27, g32p_row02_traceSegment_045_0756_0027, g32p_row02_traceSegment_045_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 810 13 14, g32p_row02_traceSegment_045_0810_0013, g32p_row02_traceSegment_045_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 837 13 14, g32p_row02_traceSegment_045_0837_0013, g32p_row02_traceSegment_045_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 810 27 27, g32p_row02_traceSegment_045_0810_0027, g32p_row02_traceSegment_045_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 756 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 756 54 54, g32p_row02_traceSegment_045_0756_0054, g32p_row02_traceSegment_045_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 648 216 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 648 108 108, g32p_row02_traceSegment_045_0648_0108, g32p_row02_traceSegment_045_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 432 432 = [0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 432 216 216, g32p_row02_traceSegment_045_0432_0216, g32p_row02_traceSegment_045_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_045 0 864 = [0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 432 432, g32p_row02_traceSegment_045_0000_0432, g32p_row02_traceSegment_045_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 864 13 14, g32p_row02_traceSegment_045_0864_0013, g32p_row02_traceSegment_045_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 891 13 14, g32p_row02_traceSegment_045_0891_0013, g32p_row02_traceSegment_045_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 864 27 27, g32p_row02_traceSegment_045_0864_0027, g32p_row02_traceSegment_045_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 918 13 14, g32p_row02_traceSegment_045_0918_0013, g32p_row02_traceSegment_045_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 945 13 14, g32p_row02_traceSegment_045_0945_0013, g32p_row02_traceSegment_045_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 918 27 27, g32p_row02_traceSegment_045_0918_0027, g32p_row02_traceSegment_045_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 864 54 54, g32p_row02_traceSegment_045_0864_0054, g32p_row02_traceSegment_045_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 972 13 14, g32p_row02_traceSegment_045_0972_0013, g32p_row02_traceSegment_045_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 999 13 14, g32p_row02_traceSegment_045_0999_0013, g32p_row02_traceSegment_045_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 972 27 27, g32p_row02_traceSegment_045_0972_0027, g32p_row02_traceSegment_045_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1026 13 14, g32p_row02_traceSegment_045_1026_0013, g32p_row02_traceSegment_045_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1053 13 14, g32p_row02_traceSegment_045_1053_0013, g32p_row02_traceSegment_045_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1026 27 27, g32p_row02_traceSegment_045_1026_0027, g32p_row02_traceSegment_045_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 972 54 54, g32p_row02_traceSegment_045_0972_0054, g32p_row02_traceSegment_045_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 864 108 108, g32p_row02_traceSegment_045_0864_0108, g32p_row02_traceSegment_045_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1080 13 14, g32p_row02_traceSegment_045_1080_0013, g32p_row02_traceSegment_045_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1107 13 14, g32p_row02_traceSegment_045_1107_0013, g32p_row02_traceSegment_045_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1080 27 27, g32p_row02_traceSegment_045_1080_0027, g32p_row02_traceSegment_045_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1134 13 14, g32p_row02_traceSegment_045_1134_0013, g32p_row02_traceSegment_045_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1161 13 14, g32p_row02_traceSegment_045_1161_0013, g32p_row02_traceSegment_045_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1134 27 27, g32p_row02_traceSegment_045_1134_0027, g32p_row02_traceSegment_045_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1080 54 54, g32p_row02_traceSegment_045_1080_0054, g32p_row02_traceSegment_045_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1188 13 14, g32p_row02_traceSegment_045_1188_0013, g32p_row02_traceSegment_045_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1215 13 14, g32p_row02_traceSegment_045_1215_0013, g32p_row02_traceSegment_045_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1188 27 27, g32p_row02_traceSegment_045_1188_0027, g32p_row02_traceSegment_045_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1242 13 14, g32p_row02_traceSegment_045_1242_0013, g32p_row02_traceSegment_045_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1269 13 14, g32p_row02_traceSegment_045_1269_0013, g32p_row02_traceSegment_045_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1242 27 27, g32p_row02_traceSegment_045_1242_0027, g32p_row02_traceSegment_045_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1188 54 54, g32p_row02_traceSegment_045_1188_0054, g32p_row02_traceSegment_045_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1080 108 108, g32p_row02_traceSegment_045_1080_0108, g32p_row02_traceSegment_045_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 864 216 216, g32p_row02_traceSegment_045_0864_0216, g32p_row02_traceSegment_045_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1296 13 14, g32p_row02_traceSegment_045_1296_0013, g32p_row02_traceSegment_045_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1323 13 14, g32p_row02_traceSegment_045_1323_0013, g32p_row02_traceSegment_045_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1296 27 27, g32p_row02_traceSegment_045_1296_0027, g32p_row02_traceSegment_045_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1350 13 14, g32p_row02_traceSegment_045_1350_0013, g32p_row02_traceSegment_045_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1377 13 14, g32p_row02_traceSegment_045_1377_0013, g32p_row02_traceSegment_045_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1350 27 27, g32p_row02_traceSegment_045_1350_0027, g32p_row02_traceSegment_045_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1296 54 54, g32p_row02_traceSegment_045_1296_0054, g32p_row02_traceSegment_045_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1404 13 14, g32p_row02_traceSegment_045_1404_0013, g32p_row02_traceSegment_045_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1431 13 14, g32p_row02_traceSegment_045_1431_0013, g32p_row02_traceSegment_045_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1404 27 27, g32p_row02_traceSegment_045_1404_0027, g32p_row02_traceSegment_045_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1458 13 14, g32p_row02_traceSegment_045_1458_0013, g32p_row02_traceSegment_045_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1485 13 14, g32p_row02_traceSegment_045_1485_0013, g32p_row02_traceSegment_045_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1458 27 27, g32p_row02_traceSegment_045_1458_0027, g32p_row02_traceSegment_045_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1404 54 54, g32p_row02_traceSegment_045_1404_0054, g32p_row02_traceSegment_045_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1296 108 108, g32p_row02_traceSegment_045_1296_0108, g32p_row02_traceSegment_045_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1512 13 14, g32p_row02_traceSegment_045_1512_0013, g32p_row02_traceSegment_045_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1539 13 14, g32p_row02_traceSegment_045_1539_0013, g32p_row02_traceSegment_045_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1512 27 27, g32p_row02_traceSegment_045_1512_0027, g32p_row02_traceSegment_045_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1566 13 14, g32p_row02_traceSegment_045_1566_0013, g32p_row02_traceSegment_045_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1593 13 = [0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1593 27 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1593 13 14, g32p_row02_traceSegment_045_1593_0013, g32p_row02_traceSegment_045_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1566 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1566 27 27, g32p_row02_traceSegment_045_1566_0027, g32p_row02_traceSegment_045_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1512 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1512 54 54, g32p_row02_traceSegment_045_1512_0054, g32p_row02_traceSegment_045_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1620 13 14, g32p_row02_traceSegment_045_1620_0013, g32p_row02_traceSegment_045_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1647 13 14, g32p_row02_traceSegment_045_1647_0013, g32p_row02_traceSegment_045_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1620 27 27, g32p_row02_traceSegment_045_1620_0027, g32p_row02_traceSegment_045_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1674 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1687 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1674 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1674 13 14, g32p_row02_traceSegment_045_1674_0013, g32p_row02_traceSegment_045_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1701 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1714 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1701 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1701 13 14, g32p_row02_traceSegment_045_1701_0013, g32p_row02_traceSegment_045_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1674 54 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1674 27 27, g32p_row02_traceSegment_045_1674_0027, g32p_row02_traceSegment_045_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1620 108 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1620 54 54, g32p_row02_traceSegment_045_1620_0054, g32p_row02_traceSegment_045_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 1512 216 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1512 108 108, g32p_row02_traceSegment_045_1512_0108, g32p_row02_traceSegment_045_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 1296 432 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1296 216 216, g32p_row02_traceSegment_045_1296_0216, g32p_row02_traceSegment_045_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_045 864 864 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 864 432 432, g32p_row02_traceSegment_045_0864_0432, g32p_row02_traceSegment_045_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_045 0 1728 = [0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 864 864, g32p_row02_traceSegment_045_0000_0864, g32p_row02_traceSegment_045_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1728 13 14, g32p_row02_traceSegment_045_1728_0013, g32p_row02_traceSegment_045_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1755 13 14, g32p_row02_traceSegment_045_1755_0013, g32p_row02_traceSegment_045_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1728 27 27, g32p_row02_traceSegment_045_1728_0027, g32p_row02_traceSegment_045_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1782 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1782 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1782 13 14, g32p_row02_traceSegment_045_1782_0013, g32p_row02_traceSegment_045_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1809 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1809 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1809 13 14, g32p_row02_traceSegment_045_1809_0013, g32p_row02_traceSegment_045_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1782 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1782 27 27, g32p_row02_traceSegment_045_1782_0027, g32p_row02_traceSegment_045_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1728 54 54, g32p_row02_traceSegment_045_1728_0054, g32p_row02_traceSegment_045_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1836 13 14, g32p_row02_traceSegment_045_1836_0013, g32p_row02_traceSegment_045_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1863 13 14, g32p_row02_traceSegment_045_1863_0013, g32p_row02_traceSegment_045_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1836 27 27, g32p_row02_traceSegment_045_1836_0027, g32p_row02_traceSegment_045_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1903 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1890 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1890 13 14, g32p_row02_traceSegment_045_1890_0013, g32p_row02_traceSegment_045_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1917 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1917 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1917 13 14, g32p_row02_traceSegment_045_1917_0013, g32p_row02_traceSegment_045_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1890 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1890 27 27, g32p_row02_traceSegment_045_1890_0027, g32p_row02_traceSegment_045_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1836 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1836 54 54, g32p_row02_traceSegment_045_1836_0054, g32p_row02_traceSegment_045_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1728 108 108, g32p_row02_traceSegment_045_1728_0108, g32p_row02_traceSegment_045_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1944 13 14, g32p_row02_traceSegment_045_1944_0013, g32p_row02_traceSegment_045_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1971 13 14, g32p_row02_traceSegment_045_1971_0013, g32p_row02_traceSegment_045_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1944 27 27, g32p_row02_traceSegment_045_1944_0027, g32p_row02_traceSegment_045_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1998 13 14, g32p_row02_traceSegment_045_1998_0013, g32p_row02_traceSegment_045_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2025 13 14, g32p_row02_traceSegment_045_2025_0013, g32p_row02_traceSegment_045_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1998 27 27, g32p_row02_traceSegment_045_1998_0027, g32p_row02_traceSegment_045_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1944 54 54, g32p_row02_traceSegment_045_1944_0054, g32p_row02_traceSegment_045_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2052 13 14, g32p_row02_traceSegment_045_2052_0013, g32p_row02_traceSegment_045_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2079 13 14, g32p_row02_traceSegment_045_2079_0013, g32p_row02_traceSegment_045_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2052 27 27, g32p_row02_traceSegment_045_2052_0027, g32p_row02_traceSegment_045_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2106 13 14, g32p_row02_traceSegment_045_2106_0013, g32p_row02_traceSegment_045_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2133 13 14, g32p_row02_traceSegment_045_2133_0013, g32p_row02_traceSegment_045_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2106 27 27, g32p_row02_traceSegment_045_2106_0027, g32p_row02_traceSegment_045_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2052 54 54, g32p_row02_traceSegment_045_2052_0054, g32p_row02_traceSegment_045_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1944 108 108, g32p_row02_traceSegment_045_1944_0108, g32p_row02_traceSegment_045_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1728 216 216, g32p_row02_traceSegment_045_1728_0216, g32p_row02_traceSegment_045_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2173 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2160 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2160 13 14, g32p_row02_traceSegment_045_2160_0013, g32p_row02_traceSegment_045_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2187 13 14, g32p_row02_traceSegment_045_2187_0013, g32p_row02_traceSegment_045_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2160 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2160 27 27, g32p_row02_traceSegment_045_2160_0027, g32p_row02_traceSegment_045_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2214 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2214 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2214 13 14, g32p_row02_traceSegment_045_2214_0013, g32p_row02_traceSegment_045_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2241 13 14, g32p_row02_traceSegment_045_2241_0013, g32p_row02_traceSegment_045_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2214 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2214 27 27, g32p_row02_traceSegment_045_2214_0027, g32p_row02_traceSegment_045_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2160 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2160 54 54, g32p_row02_traceSegment_045_2160_0054, g32p_row02_traceSegment_045_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2268 13 14, g32p_row02_traceSegment_045_2268_0013, g32p_row02_traceSegment_045_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2295 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2295 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2295 13 14, g32p_row02_traceSegment_045_2295_0013, g32p_row02_traceSegment_045_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2268 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2268 27 27, g32p_row02_traceSegment_045_2268_0027, g32p_row02_traceSegment_045_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2322 13 14, g32p_row02_traceSegment_045_2322_0013, g32p_row02_traceSegment_045_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2349 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2349 27 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2349 13 14, g32p_row02_traceSegment_045_2349_0013, g32p_row02_traceSegment_045_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2322 54 = [0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2322 27 27, g32p_row02_traceSegment_045_2322_0027, g32p_row02_traceSegment_045_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2268 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2268 54 54, g32p_row02_traceSegment_045_2268_0054, g32p_row02_traceSegment_045_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 2160 216 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2160 108 108, g32p_row02_traceSegment_045_2160_0108, g32p_row02_traceSegment_045_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2376 13 14, g32p_row02_traceSegment_045_2376_0013, g32p_row02_traceSegment_045_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2403 13 14, g32p_row02_traceSegment_045_2403_0013, g32p_row02_traceSegment_045_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2376 27 27, g32p_row02_traceSegment_045_2376_0027, g32p_row02_traceSegment_045_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2430 13 14, g32p_row02_traceSegment_045_2430_0013, g32p_row02_traceSegment_045_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2457 13 14, g32p_row02_traceSegment_045_2457_0013, g32p_row02_traceSegment_045_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2430 27 27, g32p_row02_traceSegment_045_2430_0027, g32p_row02_traceSegment_045_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2376 54 54, g32p_row02_traceSegment_045_2376_0054, g32p_row02_traceSegment_045_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2484 13 14, g32p_row02_traceSegment_045_2484_0013, g32p_row02_traceSegment_045_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2511 13 14, g32p_row02_traceSegment_045_2511_0013, g32p_row02_traceSegment_045_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2484 27 27, g32p_row02_traceSegment_045_2484_0027, g32p_row02_traceSegment_045_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2538 13 14, g32p_row02_traceSegment_045_2538_0013, g32p_row02_traceSegment_045_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2565 13 14, g32p_row02_traceSegment_045_2565_0013, g32p_row02_traceSegment_045_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2538 27 27, g32p_row02_traceSegment_045_2538_0027, g32p_row02_traceSegment_045_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2484 54 54, g32p_row02_traceSegment_045_2484_0054, g32p_row02_traceSegment_045_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2376 108 108, g32p_row02_traceSegment_045_2376_0108, g32p_row02_traceSegment_045_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 2160 432 = [0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2160 216 216, g32p_row02_traceSegment_045_2160_0216, g32p_row02_traceSegment_045_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 864 = [0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1728 432 432, g32p_row02_traceSegment_045_1728_0432, g32p_row02_traceSegment_045_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2592 13 14, g32p_row02_traceSegment_045_2592_0013, g32p_row02_traceSegment_045_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2619 13 14, g32p_row02_traceSegment_045_2619_0013, g32p_row02_traceSegment_045_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2592 27 27, g32p_row02_traceSegment_045_2592_0027, g32p_row02_traceSegment_045_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2646 13 14, g32p_row02_traceSegment_045_2646_0013, g32p_row02_traceSegment_045_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2673 13 14, g32p_row02_traceSegment_045_2673_0013, g32p_row02_traceSegment_045_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2646 27 27, g32p_row02_traceSegment_045_2646_0027, g32p_row02_traceSegment_045_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2592 54 54, g32p_row02_traceSegment_045_2592_0054, g32p_row02_traceSegment_045_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2700 13 14, g32p_row02_traceSegment_045_2700_0013, g32p_row02_traceSegment_045_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2727 13 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2740 14 = [0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2727 27 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2727 13 14, g32p_row02_traceSegment_045_2727_0013, g32p_row02_traceSegment_045_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2700 54 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2700 27 27, g32p_row02_traceSegment_045_2700_0027, g32p_row02_traceSegment_045_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2754 13 14, g32p_row02_traceSegment_045_2754_0013, g32p_row02_traceSegment_045_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2781 13 14, g32p_row02_traceSegment_045_2781_0013, g32p_row02_traceSegment_045_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2754 27 27, g32p_row02_traceSegment_045_2754_0027, g32p_row02_traceSegment_045_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2700 108 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2700 54 54, g32p_row02_traceSegment_045_2700_0054, g32p_row02_traceSegment_045_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 2592 216 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2592 108 108, g32p_row02_traceSegment_045_2592_0108, g32p_row02_traceSegment_045_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2808 13 14, g32p_row02_traceSegment_045_2808_0013, g32p_row02_traceSegment_045_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2835 13 14, g32p_row02_traceSegment_045_2835_0013, g32p_row02_traceSegment_045_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2808 27 27, g32p_row02_traceSegment_045_2808_0027, g32p_row02_traceSegment_045_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2862 13 14, g32p_row02_traceSegment_045_2862_0013, g32p_row02_traceSegment_045_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2889 13 14, g32p_row02_traceSegment_045_2889_0013, g32p_row02_traceSegment_045_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2862 27 27, g32p_row02_traceSegment_045_2862_0027, g32p_row02_traceSegment_045_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2808 54 54, g32p_row02_traceSegment_045_2808_0054, g32p_row02_traceSegment_045_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2916 13 14, g32p_row02_traceSegment_045_2916_0013, g32p_row02_traceSegment_045_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2943 13 14, g32p_row02_traceSegment_045_2943_0013, g32p_row02_traceSegment_045_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2916 27 27, g32p_row02_traceSegment_045_2916_0027, g32p_row02_traceSegment_045_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2970 13 14, g32p_row02_traceSegment_045_2970_0013, g32p_row02_traceSegment_045_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2997 13 14, g32p_row02_traceSegment_045_2997_0013, g32p_row02_traceSegment_045_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2970 27 27, g32p_row02_traceSegment_045_2970_0027, g32p_row02_traceSegment_045_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2916 54 54, g32p_row02_traceSegment_045_2916_0054, g32p_row02_traceSegment_045_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2808 108 108, g32p_row02_traceSegment_045_2808_0108, g32p_row02_traceSegment_045_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 2592 432 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2592 216 216, g32p_row02_traceSegment_045_2592_0216, g32p_row02_traceSegment_045_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3024 13 14, g32p_row02_traceSegment_045_3024_0013, g32p_row02_traceSegment_045_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3051 13 14, g32p_row02_traceSegment_045_3051_0013, g32p_row02_traceSegment_045_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3024 27 27, g32p_row02_traceSegment_045_3024_0027, g32p_row02_traceSegment_045_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3078 13 14, g32p_row02_traceSegment_045_3078_0013, g32p_row02_traceSegment_045_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3105 13 14, g32p_row02_traceSegment_045_3105_0013, g32p_row02_traceSegment_045_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3078 27 27, g32p_row02_traceSegment_045_3078_0027, g32p_row02_traceSegment_045_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3024 54 54, g32p_row02_traceSegment_045_3024_0054, g32p_row02_traceSegment_045_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3132 13 14, g32p_row02_traceSegment_045_3132_0013, g32p_row02_traceSegment_045_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3159 13 14, g32p_row02_traceSegment_045_3159_0013, g32p_row02_traceSegment_045_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3132 27 27, g32p_row02_traceSegment_045_3132_0027, g32p_row02_traceSegment_045_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3186 13 14, g32p_row02_traceSegment_045_3186_0013, g32p_row02_traceSegment_045_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3213 13 14, g32p_row02_traceSegment_045_3213_0013, g32p_row02_traceSegment_045_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3186 27 27, g32p_row02_traceSegment_045_3186_0027, g32p_row02_traceSegment_045_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3132 54 54, g32p_row02_traceSegment_045_3132_0054, g32p_row02_traceSegment_045_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3024 108 108, g32p_row02_traceSegment_045_3024_0108, g32p_row02_traceSegment_045_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3240 13 14, g32p_row02_traceSegment_045_3240_0013, g32p_row02_traceSegment_045_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3267 13 14, g32p_row02_traceSegment_045_3267_0013, g32p_row02_traceSegment_045_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3240 27 27, g32p_row02_traceSegment_045_3240_0027, g32p_row02_traceSegment_045_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3294 13 14, g32p_row02_traceSegment_045_3294_0013, g32p_row02_traceSegment_045_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3321 13 14, g32p_row02_traceSegment_045_3321_0013, g32p_row02_traceSegment_045_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3294 27 27, g32p_row02_traceSegment_045_3294_0027, g32p_row02_traceSegment_045_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3240 54 54, g32p_row02_traceSegment_045_3240_0054, g32p_row02_traceSegment_045_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3348 13 14, g32p_row02_traceSegment_045_3348_0013, g32p_row02_traceSegment_045_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3375 13 14, g32p_row02_traceSegment_045_3375_0013, g32p_row02_traceSegment_045_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3348 27 27, g32p_row02_traceSegment_045_3348_0027, g32p_row02_traceSegment_045_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3402 13 14, g32p_row02_traceSegment_045_3402_0013, g32p_row02_traceSegment_045_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_045 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_045 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_045_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_045 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3429 13 14, g32p_row02_traceSegment_045_3429_0013, g32p_row02_traceSegment_045_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_045 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3402 27 27, g32p_row02_traceSegment_045_3402_0027, g32p_row02_traceSegment_045_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_045 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3348 54 54, g32p_row02_traceSegment_045_3348_0054, g32p_row02_traceSegment_045_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_045 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3240 108 108, g32p_row02_traceSegment_045_3240_0108, g32p_row02_traceSegment_045_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_045_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_045 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 3024 216 216, g32p_row02_traceSegment_045_3024_0216, g32p_row02_traceSegment_045_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_045_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_045 2592 864 = [0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 2592 432 432, g32p_row02_traceSegment_045_2592_0432, g32p_row02_traceSegment_045_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_045_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_045 1728 1728 = [0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 1728 864 864, g32p_row02_traceSegment_045_1728_0864, g32p_row02_traceSegment_045_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_045_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_045 0 3456 = [0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_045 0 1728 1728, g32p_row02_traceSegment_045_0000_1728, g32p_row02_traceSegment_045_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_045 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 45 = [0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_045_0000_3456

end HodgeLean.Foundations.Program

end
end
