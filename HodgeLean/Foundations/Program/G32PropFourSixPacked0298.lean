import HodgeLean.Foundations.Program.G32PropFourSixPacked0291
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_030 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 30 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_030_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 13 14, g32p_row02_traceSegment_030_0000_0013, g32p_row02_traceSegment_030_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 27 13 14, g32p_row02_traceSegment_030_0027_0013, g32p_row02_traceSegment_030_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 27 27, g32p_row02_traceSegment_030_0000_0027, g32p_row02_traceSegment_030_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 54 13 14, g32p_row02_traceSegment_030_0054_0013, g32p_row02_traceSegment_030_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 94 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 81 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 81 13 14, g32p_row02_traceSegment_030_0081_0013, g32p_row02_traceSegment_030_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 54 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 54 27 27, g32p_row02_traceSegment_030_0054_0027, g32p_row02_traceSegment_030_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 0 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 54 54, g32p_row02_traceSegment_030_0000_0054, g32p_row02_traceSegment_030_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 108 13 14, g32p_row02_traceSegment_030_0108_0013, g32p_row02_traceSegment_030_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 135 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 148 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 135 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 135 13 14, g32p_row02_traceSegment_030_0135_0013, g32p_row02_traceSegment_030_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 108 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 108 27 27, g32p_row02_traceSegment_030_0108_0027, g32p_row02_traceSegment_030_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 162 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 175 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 162 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 162 13 14, g32p_row02_traceSegment_030_0162_0013, g32p_row02_traceSegment_030_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 189 13 14, g32p_row02_traceSegment_030_0189_0013, g32p_row02_traceSegment_030_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 162 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 162 27 27, g32p_row02_traceSegment_030_0162_0027, g32p_row02_traceSegment_030_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 108 108 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 108 54 54, g32p_row02_traceSegment_030_0108_0054, g32p_row02_traceSegment_030_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 0 216 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 108 108, g32p_row02_traceSegment_030_0000_0108, g32p_row02_traceSegment_030_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 216 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 216 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 216 13 14, g32p_row02_traceSegment_030_0216_0013, g32p_row02_traceSegment_030_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 243 13 14, g32p_row02_traceSegment_030_0243_0013, g32p_row02_traceSegment_030_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 216 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 216 27 27, g32p_row02_traceSegment_030_0216_0027, g32p_row02_traceSegment_030_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 270 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 283 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 270 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 270 13 14, g32p_row02_traceSegment_030_0270_0013, g32p_row02_traceSegment_030_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 297 13 14, g32p_row02_traceSegment_030_0297_0013, g32p_row02_traceSegment_030_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 270 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 270 27 27, g32p_row02_traceSegment_030_0270_0027, g32p_row02_traceSegment_030_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 216 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 216 54 54, g32p_row02_traceSegment_030_0216_0054, g32p_row02_traceSegment_030_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 324 13 14, g32p_row02_traceSegment_030_0324_0013, g32p_row02_traceSegment_030_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 364 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 351 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 351 13 14, g32p_row02_traceSegment_030_0351_0013, g32p_row02_traceSegment_030_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 324 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 324 27 27, g32p_row02_traceSegment_030_0324_0027, g32p_row02_traceSegment_030_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 378 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 391 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 378 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 378 13 14, g32p_row02_traceSegment_030_0378_0013, g32p_row02_traceSegment_030_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 418 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 405 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 405 13 14, g32p_row02_traceSegment_030_0405_0013, g32p_row02_traceSegment_030_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 378 54 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 378 27 27, g32p_row02_traceSegment_030_0378_0027, g32p_row02_traceSegment_030_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 324 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 324 54 54, g32p_row02_traceSegment_030_0324_0054, g32p_row02_traceSegment_030_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 216 216 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 216 108 108, g32p_row02_traceSegment_030_0216_0108, g32p_row02_traceSegment_030_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 0 432 = [0, 0, 0, 8, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 216 216, g32p_row02_traceSegment_030_0000_0216, g32p_row02_traceSegment_030_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 432 13 14, g32p_row02_traceSegment_030_0432_0013, g32p_row02_traceSegment_030_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 459 13 14, g32p_row02_traceSegment_030_0459_0013, g32p_row02_traceSegment_030_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 432 27 27, g32p_row02_traceSegment_030_0432_0027, g32p_row02_traceSegment_030_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 486 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 499 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 486 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 486 13 14, g32p_row02_traceSegment_030_0486_0013, g32p_row02_traceSegment_030_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 513 13 = [0, 0, 0, 2, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 526 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 513 27 = [0, 0, 0, 2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 513 13 14, g32p_row02_traceSegment_030_0513_0013, g32p_row02_traceSegment_030_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 486 54 = [0, 0, 0, 4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 486 27 27, g32p_row02_traceSegment_030_0486_0027, g32p_row02_traceSegment_030_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 432 108 = [0, 0, 0, 4, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 432 54 54, g32p_row02_traceSegment_030_0432_0054, g32p_row02_traceSegment_030_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 540 13 14, g32p_row02_traceSegment_030_0540_0013, g32p_row02_traceSegment_030_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 567 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 580 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 567 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 567 13 14, g32p_row02_traceSegment_030_0567_0013, g32p_row02_traceSegment_030_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 540 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 540 27 27, g32p_row02_traceSegment_030_0540_0027, g32p_row02_traceSegment_030_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 594 13 14, g32p_row02_traceSegment_030_0594_0013, g32p_row02_traceSegment_030_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 621 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 621 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 621 13 14, g32p_row02_traceSegment_030_0621_0013, g32p_row02_traceSegment_030_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 594 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 594 27 27, g32p_row02_traceSegment_030_0594_0027, g32p_row02_traceSegment_030_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 540 108 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 540 54 54, g32p_row02_traceSegment_030_0540_0054, g32p_row02_traceSegment_030_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 432 216 = [0, 0, 0, 7, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 432 108 108, g32p_row02_traceSegment_030_0432_0108, g32p_row02_traceSegment_030_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 661 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 648 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 648 13 14, g32p_row02_traceSegment_030_0648_0013, g32p_row02_traceSegment_030_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 675 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 688 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 675 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 675 13 14, g32p_row02_traceSegment_030_0675_0013, g32p_row02_traceSegment_030_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 648 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 648 27 27, g32p_row02_traceSegment_030_0648_0027, g32p_row02_traceSegment_030_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 702 13 14, g32p_row02_traceSegment_030_0702_0013, g32p_row02_traceSegment_030_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 729 13 14, g32p_row02_traceSegment_030_0729_0013, g32p_row02_traceSegment_030_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 702 27 27, g32p_row02_traceSegment_030_0702_0027, g32p_row02_traceSegment_030_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 648 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 648 54 54, g32p_row02_traceSegment_030_0648_0054, g32p_row02_traceSegment_030_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 756 13 14, g32p_row02_traceSegment_030_0756_0013, g32p_row02_traceSegment_030_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 796 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 783 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 783 13 14, g32p_row02_traceSegment_030_0783_0013, g32p_row02_traceSegment_030_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 756 54 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 756 27 27, g32p_row02_traceSegment_030_0756_0027, g32p_row02_traceSegment_030_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 810 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 823 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 810 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 810 13 14, g32p_row02_traceSegment_030_0810_0013, g32p_row02_traceSegment_030_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 837 13 14, g32p_row02_traceSegment_030_0837_0013, g32p_row02_traceSegment_030_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 810 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 810 27 27, g32p_row02_traceSegment_030_0810_0027, g32p_row02_traceSegment_030_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 756 108 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 756 54 54, g32p_row02_traceSegment_030_0756_0054, g32p_row02_traceSegment_030_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 648 216 = [0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 648 108 108, g32p_row02_traceSegment_030_0648_0108, g32p_row02_traceSegment_030_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 432 432 = [0, 0, 0, 14, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 432 216 216, g32p_row02_traceSegment_030_0432_0216, g32p_row02_traceSegment_030_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_030 0 864 = [0, 0, 0, 22, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 432 432, g32p_row02_traceSegment_030_0000_0432, g32p_row02_traceSegment_030_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 864 13 14, g32p_row02_traceSegment_030_0864_0013, g32p_row02_traceSegment_030_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 891 13 14, g32p_row02_traceSegment_030_0891_0013, g32p_row02_traceSegment_030_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 864 27 27, g32p_row02_traceSegment_030_0864_0027, g32p_row02_traceSegment_030_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 918 13 14, g32p_row02_traceSegment_030_0918_0013, g32p_row02_traceSegment_030_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 945 13 14, g32p_row02_traceSegment_030_0945_0013, g32p_row02_traceSegment_030_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 918 27 27, g32p_row02_traceSegment_030_0918_0027, g32p_row02_traceSegment_030_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 864 54 54, g32p_row02_traceSegment_030_0864_0054, g32p_row02_traceSegment_030_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 972 13 14, g32p_row02_traceSegment_030_0972_0013, g32p_row02_traceSegment_030_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 999 13 14, g32p_row02_traceSegment_030_0999_0013, g32p_row02_traceSegment_030_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 972 27 27, g32p_row02_traceSegment_030_0972_0027, g32p_row02_traceSegment_030_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1026 13 14, g32p_row02_traceSegment_030_1026_0013, g32p_row02_traceSegment_030_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1053 13 14, g32p_row02_traceSegment_030_1053_0013, g32p_row02_traceSegment_030_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1026 27 27, g32p_row02_traceSegment_030_1026_0027, g32p_row02_traceSegment_030_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 972 54 54, g32p_row02_traceSegment_030_0972_0054, g32p_row02_traceSegment_030_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 864 108 108, g32p_row02_traceSegment_030_0864_0108, g32p_row02_traceSegment_030_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1080 13 14, g32p_row02_traceSegment_030_1080_0013, g32p_row02_traceSegment_030_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1107 13 14, g32p_row02_traceSegment_030_1107_0013, g32p_row02_traceSegment_030_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1080 27 27, g32p_row02_traceSegment_030_1080_0027, g32p_row02_traceSegment_030_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1134 13 14, g32p_row02_traceSegment_030_1134_0013, g32p_row02_traceSegment_030_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1161 13 14, g32p_row02_traceSegment_030_1161_0013, g32p_row02_traceSegment_030_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1134 27 27, g32p_row02_traceSegment_030_1134_0027, g32p_row02_traceSegment_030_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1080 54 54, g32p_row02_traceSegment_030_1080_0054, g32p_row02_traceSegment_030_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1188 13 14, g32p_row02_traceSegment_030_1188_0013, g32p_row02_traceSegment_030_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1215 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1228 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1215 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1215 13 14, g32p_row02_traceSegment_030_1215_0013, g32p_row02_traceSegment_030_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1188 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1188 27 27, g32p_row02_traceSegment_030_1188_0027, g32p_row02_traceSegment_030_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1255 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1242 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1242 13 14, g32p_row02_traceSegment_030_1242_0013, g32p_row02_traceSegment_030_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1269 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1269 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1269 13 14, g32p_row02_traceSegment_030_1269_0013, g32p_row02_traceSegment_030_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1242 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1242 27 27, g32p_row02_traceSegment_030_1242_0027, g32p_row02_traceSegment_030_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1188 108 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1188 54 54, g32p_row02_traceSegment_030_1188_0054, g32p_row02_traceSegment_030_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 1080 216 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1080 108 108, g32p_row02_traceSegment_030_1080_0108, g32p_row02_traceSegment_030_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 864 432 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 864 216 216, g32p_row02_traceSegment_030_0864_0216, g32p_row02_traceSegment_030_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1296 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1296 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1296 13 14, g32p_row02_traceSegment_030_1296_0013, g32p_row02_traceSegment_030_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1323 13 14, g32p_row02_traceSegment_030_1323_0013, g32p_row02_traceSegment_030_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1296 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1296 27 27, g32p_row02_traceSegment_030_1296_0027, g32p_row02_traceSegment_030_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1350 13 14, g32p_row02_traceSegment_030_1350_0013, g32p_row02_traceSegment_030_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1390 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1377 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1377 13 14, g32p_row02_traceSegment_030_1377_0013, g32p_row02_traceSegment_030_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1350 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1350 27 27, g32p_row02_traceSegment_030_1350_0027, g32p_row02_traceSegment_030_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1296 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1296 54 54, g32p_row02_traceSegment_030_1296_0054, g32p_row02_traceSegment_030_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1404 13 14, g32p_row02_traceSegment_030_1404_0013, g32p_row02_traceSegment_030_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1431 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1431 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1431 13 14, g32p_row02_traceSegment_030_1431_0013, g32p_row02_traceSegment_030_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1404 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1404 27 27, g32p_row02_traceSegment_030_1404_0027, g32p_row02_traceSegment_030_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1458 13 14, g32p_row02_traceSegment_030_1458_0013, g32p_row02_traceSegment_030_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1498 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1485 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1485 13 14, g32p_row02_traceSegment_030_1485_0013, g32p_row02_traceSegment_030_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1458 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1458 27 27, g32p_row02_traceSegment_030_1458_0027, g32p_row02_traceSegment_030_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1404 108 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1404 54 54, g32p_row02_traceSegment_030_1404_0054, g32p_row02_traceSegment_030_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 1296 216 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1296 108 108, g32p_row02_traceSegment_030_1296_0108, g32p_row02_traceSegment_030_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1512 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1512 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1512 13 14, g32p_row02_traceSegment_030_1512_0013, g32p_row02_traceSegment_030_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1539 13 14, g32p_row02_traceSegment_030_1539_0013, g32p_row02_traceSegment_030_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1512 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1512 27 27, g32p_row02_traceSegment_030_1512_0027, g32p_row02_traceSegment_030_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1566 13 14, g32p_row02_traceSegment_030_1566_0013, g32p_row02_traceSegment_030_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1593 13 14, g32p_row02_traceSegment_030_1593_0013, g32p_row02_traceSegment_030_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1566 27 27, g32p_row02_traceSegment_030_1566_0027, g32p_row02_traceSegment_030_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1512 108 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1512 54 54, g32p_row02_traceSegment_030_1512_0054, g32p_row02_traceSegment_030_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1620 13 14, g32p_row02_traceSegment_030_1620_0013, g32p_row02_traceSegment_030_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1647 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1660 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1647 27 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1647 13 14, g32p_row02_traceSegment_030_1647_0013, g32p_row02_traceSegment_030_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1620 54 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1620 27 27, g32p_row02_traceSegment_030_1620_0027, g32p_row02_traceSegment_030_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1674 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1674 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1674 13 14, g32p_row02_traceSegment_030_1674_0013, g32p_row02_traceSegment_030_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1714 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1701 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1701 13 14, g32p_row02_traceSegment_030_1701_0013, g32p_row02_traceSegment_030_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1674 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1674 27 27, g32p_row02_traceSegment_030_1674_0027, g32p_row02_traceSegment_030_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1620 108 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1620 54 54, g32p_row02_traceSegment_030_1620_0054, g32p_row02_traceSegment_030_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 1512 216 = [0, 0, 0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1512 108 108, g32p_row02_traceSegment_030_1512_0108, g32p_row02_traceSegment_030_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 1296 432 = [0, 0, 0, 0, 0, 17] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1296 216 216, g32p_row02_traceSegment_030_1296_0216, g32p_row02_traceSegment_030_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_030 864 864 = [0, 0, 0, 0, 0, 22] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 864 432 432, g32p_row02_traceSegment_030_0864_0432, g32p_row02_traceSegment_030_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_030 0 1728 = [0, 0, 0, 22, 0, 30] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 864 864, g32p_row02_traceSegment_030_0000_0864, g32p_row02_traceSegment_030_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1741 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 27 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1728 13 14, g32p_row02_traceSegment_030_1728_0013, g32p_row02_traceSegment_030_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1755 13 14, g32p_row02_traceSegment_030_1755_0013, g32p_row02_traceSegment_030_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 54 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1728 27 27, g32p_row02_traceSegment_030_1728_0027, g32p_row02_traceSegment_030_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1782 13 14, g32p_row02_traceSegment_030_1782_0013, g32p_row02_traceSegment_030_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1809 13 14, g32p_row02_traceSegment_030_1809_0013, g32p_row02_traceSegment_030_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1782 27 27, g32p_row02_traceSegment_030_1782_0027, g32p_row02_traceSegment_030_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 108 = [0, 0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1728 54 54, g32p_row02_traceSegment_030_1728_0054, g32p_row02_traceSegment_030_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1836 13 14, g32p_row02_traceSegment_030_1836_0013, g32p_row02_traceSegment_030_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1863 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1876 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1863 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1863 13 14, g32p_row02_traceSegment_030_1863_0013, g32p_row02_traceSegment_030_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1836 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1836 27 27, g32p_row02_traceSegment_030_1836_0027, g32p_row02_traceSegment_030_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1890 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1903 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1890 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1890 13 14, g32p_row02_traceSegment_030_1890_0013, g32p_row02_traceSegment_030_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1930 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1917 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1917 13 14, g32p_row02_traceSegment_030_1917_0013, g32p_row02_traceSegment_030_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1890 54 = [0, 0, 0, 2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1890 27 27, g32p_row02_traceSegment_030_1890_0027, g32p_row02_traceSegment_030_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1836 108 = [0, 0, 0, 2, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1836 54 54, g32p_row02_traceSegment_030_1836_0054, g32p_row02_traceSegment_030_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 216 = [0, 0, 0, 2, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1728 108 108, g32p_row02_traceSegment_030_1728_0108, g32p_row02_traceSegment_030_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1944 13 = [0, 0, 0, 1, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1957 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1944 27 = [0, 0, 0, 2, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1944 13 14, g32p_row02_traceSegment_030_1944_0013, g32p_row02_traceSegment_030_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1971 13 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 1984 14 = [0, 0, 0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1971 27 = [0, 0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1971 13 14, g32p_row02_traceSegment_030_1971_0013, g32p_row02_traceSegment_030_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1944 54 = [0, 0, 0, 2, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1944 27 27, g32p_row02_traceSegment_030_1944_0027, g32p_row02_traceSegment_030_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 1998 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2011 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 1998 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1998 13 14, g32p_row02_traceSegment_030_1998_0013, g32p_row02_traceSegment_030_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2025 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2025 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2025 13 14, g32p_row02_traceSegment_030_2025_0013, g32p_row02_traceSegment_030_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 1998 54 = [0, 0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1998 27 27, g32p_row02_traceSegment_030_1998_0027, g32p_row02_traceSegment_030_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 1944 108 = [0, 0, 0, 2, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1944 54 54, g32p_row02_traceSegment_030_1944_0054, g32p_row02_traceSegment_030_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2052 13 14, g32p_row02_traceSegment_030_2052_0013, g32p_row02_traceSegment_030_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2079 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2092 14 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2079 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2079 13 14, g32p_row02_traceSegment_030_2079_0013, g32p_row02_traceSegment_030_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2052 54 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2052 27 27, g32p_row02_traceSegment_030_2052_0027, g32p_row02_traceSegment_030_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2106 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2119 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2106 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2106 13 14, g32p_row02_traceSegment_030_2106_0013, g32p_row02_traceSegment_030_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2133 13 = [0, 0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2146 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2133 27 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2133 13 14, g32p_row02_traceSegment_030_2133_0013, g32p_row02_traceSegment_030_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2106 54 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2106 27 27, g32p_row02_traceSegment_030_2106_0027, g32p_row02_traceSegment_030_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2052 108 = [0, 0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2052 54 54, g32p_row02_traceSegment_030_2052_0054, g32p_row02_traceSegment_030_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 1944 216 = [0, 0, 0, 2, 0, 33] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1944 108 108, g32p_row02_traceSegment_030_1944_0108, g32p_row02_traceSegment_030_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 432 = [0, 0, 0, 4, 0, 45] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1728 216 216, g32p_row02_traceSegment_030_1728_0216, g32p_row02_traceSegment_030_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2160 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2160 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2160 13 14, g32p_row02_traceSegment_030_2160_0013, g32p_row02_traceSegment_030_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2200 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2187 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2187 13 14, g32p_row02_traceSegment_030_2187_0013, g32p_row02_traceSegment_030_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2160 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2160 27 27, g32p_row02_traceSegment_030_2160_0027, g32p_row02_traceSegment_030_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2214 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2214 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2214 13 14, g32p_row02_traceSegment_030_2214_0013, g32p_row02_traceSegment_030_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2241 13 14, g32p_row02_traceSegment_030_2241_0013, g32p_row02_traceSegment_030_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2214 54 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2214 27 27, g32p_row02_traceSegment_030_2214_0027, g32p_row02_traceSegment_030_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2160 108 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2160 54 54, g32p_row02_traceSegment_030_2160_0054, g32p_row02_traceSegment_030_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2268 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2268 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2268 13 14, g32p_row02_traceSegment_030_2268_0013, g32p_row02_traceSegment_030_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2295 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2308 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2295 27 = [0, 0, 0, 1, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2295 13 14, g32p_row02_traceSegment_030_2295_0013, g32p_row02_traceSegment_030_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2268 54 = [0, 0, 0, 2, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2268 27 27, g32p_row02_traceSegment_030_2268_0027, g32p_row02_traceSegment_030_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2322 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2335 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2322 27 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2322 13 14, g32p_row02_traceSegment_030_2322_0013, g32p_row02_traceSegment_030_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2349 13 14, g32p_row02_traceSegment_030_2349_0013, g32p_row02_traceSegment_030_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2322 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2322 27 27, g32p_row02_traceSegment_030_2322_0027, g32p_row02_traceSegment_030_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2268 108 = [0, 0, 0, 2, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2268 54 54, g32p_row02_traceSegment_030_2268_0054, g32p_row02_traceSegment_030_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 2160 216 = [0, 0, 0, 2, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2160 108 108, g32p_row02_traceSegment_030_2160_0108, g32p_row02_traceSegment_030_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2389 14 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2376 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2376 13 14, g32p_row02_traceSegment_030_2376_0013, g32p_row02_traceSegment_030_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2403 13 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2416 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2403 27 = [0, 0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2403 13 14, g32p_row02_traceSegment_030_2403_0013, g32p_row02_traceSegment_030_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2376 54 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2376 27 27, g32p_row02_traceSegment_030_2376_0027, g32p_row02_traceSegment_030_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2430 13 14, g32p_row02_traceSegment_030_2430_0013, g32p_row02_traceSegment_030_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2457 13 14, g32p_row02_traceSegment_030_2457_0013, g32p_row02_traceSegment_030_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2430 27 27, g32p_row02_traceSegment_030_2430_0027, g32p_row02_traceSegment_030_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2376 108 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2376 54 54, g32p_row02_traceSegment_030_2376_0054, g32p_row02_traceSegment_030_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2484 13 14, g32p_row02_traceSegment_030_2484_0013, g32p_row02_traceSegment_030_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2524 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2511 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2511 13 14, g32p_row02_traceSegment_030_2511_0013, g32p_row02_traceSegment_030_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2484 54 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2484 27 27, g32p_row02_traceSegment_030_2484_0027, g32p_row02_traceSegment_030_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2538 13 = [0, 0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2538 27 = [0, 0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2538 13 14, g32p_row02_traceSegment_030_2538_0013, g32p_row02_traceSegment_030_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2578 14 = [0, 0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2565 27 = [0, 0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2565 13 14, g32p_row02_traceSegment_030_2565_0013, g32p_row02_traceSegment_030_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2538 54 = [0, 0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2538 27 27, g32p_row02_traceSegment_030_2538_0027, g32p_row02_traceSegment_030_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2484 108 = [0, 0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2484 54 54, g32p_row02_traceSegment_030_2484_0054, g32p_row02_traceSegment_030_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 2376 216 = [0, 0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2376 108 108, g32p_row02_traceSegment_030_2376_0108, g32p_row02_traceSegment_030_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 2160 432 = [0, 0, 0, 2, 0, 19] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2160 216 216, g32p_row02_traceSegment_030_2160_0216, g32p_row02_traceSegment_030_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 864 = [0, 0, 0, 6, 0, 64] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1728 432 432, g32p_row02_traceSegment_030_1728_0432, g32p_row02_traceSegment_030_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2592 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2605 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2592 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2592 13 14, g32p_row02_traceSegment_030_2592_0013, g32p_row02_traceSegment_030_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2619 13 = [0, 0, 0, 1, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2619 27 = [0, 0, 0, 1, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2619 13 14, g32p_row02_traceSegment_030_2619_0013, g32p_row02_traceSegment_030_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2592 54 = [0, 0, 0, 6, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2592 27 27, g32p_row02_traceSegment_030_2592_0027, g32p_row02_traceSegment_030_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2646 13 14, g32p_row02_traceSegment_030_2646_0013, g32p_row02_traceSegment_030_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2673 13 14, g32p_row02_traceSegment_030_2673_0013, g32p_row02_traceSegment_030_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2646 27 27, g32p_row02_traceSegment_030_2646_0027, g32p_row02_traceSegment_030_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2592 108 = [0, 0, 0, 6, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2592 54 54, g32p_row02_traceSegment_030_2592_0054, g32p_row02_traceSegment_030_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2700 13 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2713 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2700 27 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2700 13 14, g32p_row02_traceSegment_030_2700_0013, g32p_row02_traceSegment_030_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2727 13 14, g32p_row02_traceSegment_030_2727_0013, g32p_row02_traceSegment_030_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2700 54 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2700 27 27, g32p_row02_traceSegment_030_2700_0027, g32p_row02_traceSegment_030_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2754 13 14, g32p_row02_traceSegment_030_2754_0013, g32p_row02_traceSegment_030_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2781 13 14, g32p_row02_traceSegment_030_2781_0013, g32p_row02_traceSegment_030_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2754 27 27, g32p_row02_traceSegment_030_2754_0027, g32p_row02_traceSegment_030_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2700 108 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2700 54 54, g32p_row02_traceSegment_030_2700_0054, g32p_row02_traceSegment_030_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 2592 216 = [0, 0, 0, 12, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2592 108 108, g32p_row02_traceSegment_030_2592_0108, g32p_row02_traceSegment_030_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2808 13 14, g32p_row02_traceSegment_030_2808_0013, g32p_row02_traceSegment_030_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2835 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2848 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2835 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2835 13 14, g32p_row02_traceSegment_030_2835_0013, g32p_row02_traceSegment_030_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2808 54 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2808 27 27, g32p_row02_traceSegment_030_2808_0027, g32p_row02_traceSegment_030_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2862 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2875 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2862 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2862 13 14, g32p_row02_traceSegment_030_2862_0013, g32p_row02_traceSegment_030_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2889 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2902 14 = [0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2889 27 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2889 13 14, g32p_row02_traceSegment_030_2889_0013, g32p_row02_traceSegment_030_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2862 54 = [0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2862 27 27, g32p_row02_traceSegment_030_2862_0027, g32p_row02_traceSegment_030_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2808 108 = [0, 0, 0, 15] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2808 54 54, g32p_row02_traceSegment_030_2808_0054, g32p_row02_traceSegment_030_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2916 13 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2916 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2916 13 14, g32p_row02_traceSegment_030_2916_0013, g32p_row02_traceSegment_030_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2943 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2956 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2943 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2943 13 14, g32p_row02_traceSegment_030_2943_0013, g32p_row02_traceSegment_030_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2916 54 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2916 27 27, g32p_row02_traceSegment_030_2916_0027, g32p_row02_traceSegment_030_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 2983 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2970 27 = [0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2970 13 14, g32p_row02_traceSegment_030_2970_0013, g32p_row02_traceSegment_030_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3010 14 = [0, 0, 0, 4] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 2997 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2997 13 14, g32p_row02_traceSegment_030_2997_0013, g32p_row02_traceSegment_030_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 2970 54 = [0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2970 27 27, g32p_row02_traceSegment_030_2970_0027, g32p_row02_traceSegment_030_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 2916 108 = [0, 0, 0, 11] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2916 54 54, g32p_row02_traceSegment_030_2916_0054, g32p_row02_traceSegment_030_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 2808 216 = [0, 0, 0, 26] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2808 108 108, g32p_row02_traceSegment_030_2808_0108, g32p_row02_traceSegment_030_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 2592 432 = [0, 0, 0, 38, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2592 216 216, g32p_row02_traceSegment_030_2592_0216, g32p_row02_traceSegment_030_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3024 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3037 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3024 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3024 13 14, g32p_row02_traceSegment_030_3024_0013, g32p_row02_traceSegment_030_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3051 13 = [0, 0, 0, 6] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3064 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3051 27 = [0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3051 13 14, g32p_row02_traceSegment_030_3051_0013, g32p_row02_traceSegment_030_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3024 54 = [0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3024 27 27, g32p_row02_traceSegment_030_3024_0027, g32p_row02_traceSegment_030_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3078 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3091 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3078 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3078 13 14, g32p_row02_traceSegment_030_3078_0013, g32p_row02_traceSegment_030_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3105 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3118 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3105 27 = [0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3105 13 14, g32p_row02_traceSegment_030_3105_0013, g32p_row02_traceSegment_030_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3078 54 = [0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3078 27 27, g32p_row02_traceSegment_030_3078_0027, g32p_row02_traceSegment_030_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 3024 108 = [0, 0, 0, 18] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3024 54 54, g32p_row02_traceSegment_030_3024_0054, g32p_row02_traceSegment_030_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3132 13 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3145 14 = [0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3132 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3132 13 14, g32p_row02_traceSegment_030_3132_0013, g32p_row02_traceSegment_030_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3159 13 14, g32p_row02_traceSegment_030_3159_0013, g32p_row02_traceSegment_030_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3132 54 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3132 27 27, g32p_row02_traceSegment_030_3132_0027, g32p_row02_traceSegment_030_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3186 13 = [0, 0, 0, 2, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3186 27 = [0, 0, 0, 2, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3186 13 14, g32p_row02_traceSegment_030_3186_0013, g32p_row02_traceSegment_030_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3213 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3226 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3213 27 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3213 13 14, g32p_row02_traceSegment_030_3213_0013, g32p_row02_traceSegment_030_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3186 54 = [0, 0, 0, 6, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3186 27 27, g32p_row02_traceSegment_030_3186_0027, g32p_row02_traceSegment_030_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 3132 108 = [0, 0, 0, 8, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3132 54 54, g32p_row02_traceSegment_030_3132_0054, g32p_row02_traceSegment_030_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 3024 216 = [0, 0, 0, 26, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3024 108 108, g32p_row02_traceSegment_030_3024_0108, g32p_row02_traceSegment_030_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3253 14 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3240 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3240 13 14, g32p_row02_traceSegment_030_3240_0013, g32p_row02_traceSegment_030_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3267 13 = [0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3267 27 = [0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3267 13 14, g32p_row02_traceSegment_030_3267_0013, g32p_row02_traceSegment_030_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3240 54 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3240 27 27, g32p_row02_traceSegment_030_3240_0027, g32p_row02_traceSegment_030_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3294 13 14, g32p_row02_traceSegment_030_3294_0013, g32p_row02_traceSegment_030_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3321 13 14, g32p_row02_traceSegment_030_3321_0013, g32p_row02_traceSegment_030_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3294 27 27, g32p_row02_traceSegment_030_3294_0027, g32p_row02_traceSegment_030_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 3240 108 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3240 54 54, g32p_row02_traceSegment_030_3240_0054, g32p_row02_traceSegment_030_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3348 13 14, g32p_row02_traceSegment_030_3348_0013, g32p_row02_traceSegment_030_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3375 13 14, g32p_row02_traceSegment_030_3375_0013, g32p_row02_traceSegment_030_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3348 27 27, g32p_row02_traceSegment_030_3348_0027, g32p_row02_traceSegment_030_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3402 13 14, g32p_row02_traceSegment_030_3402_0013, g32p_row02_traceSegment_030_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_030 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_030 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_030_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_030 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3429 13 14, g32p_row02_traceSegment_030_3429_0013, g32p_row02_traceSegment_030_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_030 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3402 27 27, g32p_row02_traceSegment_030_3402_0027, g32p_row02_traceSegment_030_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_030 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3348 54 54, g32p_row02_traceSegment_030_3348_0054, g32p_row02_traceSegment_030_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_030 3240 216 = [0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3240 108 108, g32p_row02_traceSegment_030_3240_0108, g32p_row02_traceSegment_030_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_030_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_030 3024 432 = [0, 0, 0, 30, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 3024 216 216, g32p_row02_traceSegment_030_3024_0216, g32p_row02_traceSegment_030_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_030_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_030 2592 864 = [0, 0, 0, 68, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 2592 432 432, g32p_row02_traceSegment_030_2592_0432, g32p_row02_traceSegment_030_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_030_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_030 1728 1728 = [0, 0, 0, 74, 0, 66] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 1728 864 864, g32p_row02_traceSegment_030_1728_0864, g32p_row02_traceSegment_030_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_030_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_030 0 3456 = [0, 0, 0, 96, 0, 96] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_030 0 1728 1728, g32p_row02_traceSegment_030_0000_1728, g32p_row02_traceSegment_030_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_030 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 30 = [0, 0, 0, 96, 0, 96] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_030_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_031 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 31 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_031_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 0 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 0 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 13 14, g32p_row02_traceSegment_031_0000_0013, g32p_row02_traceSegment_031_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 27 13 14, g32p_row02_traceSegment_031_0027_0013, g32p_row02_traceSegment_031_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 0 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 27 27, g32p_row02_traceSegment_031_0000_0027, g32p_row02_traceSegment_031_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 54 13 14, g32p_row02_traceSegment_031_0054_0013, g32p_row02_traceSegment_031_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 81 13 14, g32p_row02_traceSegment_031_0081_0013, g32p_row02_traceSegment_031_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 54 27 27, g32p_row02_traceSegment_031_0054_0027, g32p_row02_traceSegment_031_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 0 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 54 54, g32p_row02_traceSegment_031_0000_0054, g32p_row02_traceSegment_031_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 108 13 14, g32p_row02_traceSegment_031_0108_0013, g32p_row02_traceSegment_031_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 135 13 14, g32p_row02_traceSegment_031_0135_0013, g32p_row02_traceSegment_031_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 108 27 27, g32p_row02_traceSegment_031_0108_0027, g32p_row02_traceSegment_031_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 162 13 14, g32p_row02_traceSegment_031_0162_0013, g32p_row02_traceSegment_031_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 189 13 14, g32p_row02_traceSegment_031_0189_0013, g32p_row02_traceSegment_031_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 162 27 27, g32p_row02_traceSegment_031_0162_0027, g32p_row02_traceSegment_031_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 108 54 54, g32p_row02_traceSegment_031_0108_0054, g32p_row02_traceSegment_031_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 0 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 108 108, g32p_row02_traceSegment_031_0000_0108, g32p_row02_traceSegment_031_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 216 13 14, g32p_row02_traceSegment_031_0216_0013, g32p_row02_traceSegment_031_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 243 13 14, g32p_row02_traceSegment_031_0243_0013, g32p_row02_traceSegment_031_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 216 27 27, g32p_row02_traceSegment_031_0216_0027, g32p_row02_traceSegment_031_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 270 13 14, g32p_row02_traceSegment_031_0270_0013, g32p_row02_traceSegment_031_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 297 13 14, g32p_row02_traceSegment_031_0297_0013, g32p_row02_traceSegment_031_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 270 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 270 27 27, g32p_row02_traceSegment_031_0270_0027, g32p_row02_traceSegment_031_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 216 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 216 54 54, g32p_row02_traceSegment_031_0216_0054, g32p_row02_traceSegment_031_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 324 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 324 13 14, g32p_row02_traceSegment_031_0324_0013, g32p_row02_traceSegment_031_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 351 13 14, g32p_row02_traceSegment_031_0351_0013, g32p_row02_traceSegment_031_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 324 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 324 27 27, g32p_row02_traceSegment_031_0324_0027, g32p_row02_traceSegment_031_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 378 13 14, g32p_row02_traceSegment_031_0378_0013, g32p_row02_traceSegment_031_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 405 13 14, g32p_row02_traceSegment_031_0405_0013, g32p_row02_traceSegment_031_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 378 27 27, g32p_row02_traceSegment_031_0378_0027, g32p_row02_traceSegment_031_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 324 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 324 54 54, g32p_row02_traceSegment_031_0324_0054, g32p_row02_traceSegment_031_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 216 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 216 108 108, g32p_row02_traceSegment_031_0216_0108, g32p_row02_traceSegment_031_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 0 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 216 216, g32p_row02_traceSegment_031_0000_0216, g32p_row02_traceSegment_031_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 432 13 14, g32p_row02_traceSegment_031_0432_0013, g32p_row02_traceSegment_031_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 459 13 14, g32p_row02_traceSegment_031_0459_0013, g32p_row02_traceSegment_031_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 432 27 27, g32p_row02_traceSegment_031_0432_0027, g32p_row02_traceSegment_031_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 486 13 14, g32p_row02_traceSegment_031_0486_0013, g32p_row02_traceSegment_031_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 513 13 14, g32p_row02_traceSegment_031_0513_0013, g32p_row02_traceSegment_031_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 486 27 27, g32p_row02_traceSegment_031_0486_0027, g32p_row02_traceSegment_031_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 432 54 54, g32p_row02_traceSegment_031_0432_0054, g32p_row02_traceSegment_031_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 540 13 14, g32p_row02_traceSegment_031_0540_0013, g32p_row02_traceSegment_031_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 567 13 14, g32p_row02_traceSegment_031_0567_0013, g32p_row02_traceSegment_031_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 540 27 27, g32p_row02_traceSegment_031_0540_0027, g32p_row02_traceSegment_031_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 594 13 14, g32p_row02_traceSegment_031_0594_0013, g32p_row02_traceSegment_031_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 621 13 14, g32p_row02_traceSegment_031_0621_0013, g32p_row02_traceSegment_031_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 594 27 27, g32p_row02_traceSegment_031_0594_0027, g32p_row02_traceSegment_031_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 540 54 54, g32p_row02_traceSegment_031_0540_0054, g32p_row02_traceSegment_031_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 432 108 108, g32p_row02_traceSegment_031_0432_0108, g32p_row02_traceSegment_031_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 648 13 14, g32p_row02_traceSegment_031_0648_0013, g32p_row02_traceSegment_031_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 675 13 14, g32p_row02_traceSegment_031_0675_0013, g32p_row02_traceSegment_031_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 648 27 27, g32p_row02_traceSegment_031_0648_0027, g32p_row02_traceSegment_031_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 702 13 14, g32p_row02_traceSegment_031_0702_0013, g32p_row02_traceSegment_031_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 729 13 14, g32p_row02_traceSegment_031_0729_0013, g32p_row02_traceSegment_031_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 702 27 27, g32p_row02_traceSegment_031_0702_0027, g32p_row02_traceSegment_031_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 648 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 648 54 54, g32p_row02_traceSegment_031_0648_0054, g32p_row02_traceSegment_031_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 756 13 14, g32p_row02_traceSegment_031_0756_0013, g32p_row02_traceSegment_031_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 783 13 14, g32p_row02_traceSegment_031_0783_0013, g32p_row02_traceSegment_031_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 756 27 27, g32p_row02_traceSegment_031_0756_0027, g32p_row02_traceSegment_031_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 810 13 14, g32p_row02_traceSegment_031_0810_0013, g32p_row02_traceSegment_031_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 837 13 14, g32p_row02_traceSegment_031_0837_0013, g32p_row02_traceSegment_031_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 810 27 27, g32p_row02_traceSegment_031_0810_0027, g32p_row02_traceSegment_031_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 756 54 54, g32p_row02_traceSegment_031_0756_0054, g32p_row02_traceSegment_031_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 648 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 648 108 108, g32p_row02_traceSegment_031_0648_0108, g32p_row02_traceSegment_031_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 432 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 432 216 216, g32p_row02_traceSegment_031_0432_0216, g32p_row02_traceSegment_031_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_031 0 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 432 432, g32p_row02_traceSegment_031_0000_0432, g32p_row02_traceSegment_031_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 864 13 14, g32p_row02_traceSegment_031_0864_0013, g32p_row02_traceSegment_031_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 891 13 14, g32p_row02_traceSegment_031_0891_0013, g32p_row02_traceSegment_031_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 864 27 27, g32p_row02_traceSegment_031_0864_0027, g32p_row02_traceSegment_031_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 918 13 14, g32p_row02_traceSegment_031_0918_0013, g32p_row02_traceSegment_031_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 945 13 14, g32p_row02_traceSegment_031_0945_0013, g32p_row02_traceSegment_031_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 918 27 27, g32p_row02_traceSegment_031_0918_0027, g32p_row02_traceSegment_031_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 864 54 54, g32p_row02_traceSegment_031_0864_0054, g32p_row02_traceSegment_031_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 972 13 14, g32p_row02_traceSegment_031_0972_0013, g32p_row02_traceSegment_031_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 999 13 14, g32p_row02_traceSegment_031_0999_0013, g32p_row02_traceSegment_031_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 972 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 972 27 27, g32p_row02_traceSegment_031_0972_0027, g32p_row02_traceSegment_031_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1026 13 14, g32p_row02_traceSegment_031_1026_0013, g32p_row02_traceSegment_031_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1053 13 14, g32p_row02_traceSegment_031_1053_0013, g32p_row02_traceSegment_031_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1026 27 27, g32p_row02_traceSegment_031_1026_0027, g32p_row02_traceSegment_031_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 972 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 972 54 54, g32p_row02_traceSegment_031_0972_0054, g32p_row02_traceSegment_031_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 864 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 864 108 108, g32p_row02_traceSegment_031_0864_0108, g32p_row02_traceSegment_031_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1080 13 14, g32p_row02_traceSegment_031_1080_0013, g32p_row02_traceSegment_031_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1107 13 14, g32p_row02_traceSegment_031_1107_0013, g32p_row02_traceSegment_031_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1080 27 27, g32p_row02_traceSegment_031_1080_0027, g32p_row02_traceSegment_031_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1134 13 14, g32p_row02_traceSegment_031_1134_0013, g32p_row02_traceSegment_031_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1161 13 14, g32p_row02_traceSegment_031_1161_0013, g32p_row02_traceSegment_031_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1134 27 27, g32p_row02_traceSegment_031_1134_0027, g32p_row02_traceSegment_031_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1080 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1080 54 54, g32p_row02_traceSegment_031_1080_0054, g32p_row02_traceSegment_031_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1188 13 14, g32p_row02_traceSegment_031_1188_0013, g32p_row02_traceSegment_031_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1215 13 14, g32p_row02_traceSegment_031_1215_0013, g32p_row02_traceSegment_031_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1188 27 27, g32p_row02_traceSegment_031_1188_0027, g32p_row02_traceSegment_031_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1242 13 14, g32p_row02_traceSegment_031_1242_0013, g32p_row02_traceSegment_031_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1269 13 14, g32p_row02_traceSegment_031_1269_0013, g32p_row02_traceSegment_031_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1242 27 27, g32p_row02_traceSegment_031_1242_0027, g32p_row02_traceSegment_031_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1188 54 54, g32p_row02_traceSegment_031_1188_0054, g32p_row02_traceSegment_031_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 1080 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1080 108 108, g32p_row02_traceSegment_031_1080_0108, g32p_row02_traceSegment_031_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 864 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 864 216 216, g32p_row02_traceSegment_031_0864_0216, g32p_row02_traceSegment_031_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1296 13 14, g32p_row02_traceSegment_031_1296_0013, g32p_row02_traceSegment_031_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1323 13 14, g32p_row02_traceSegment_031_1323_0013, g32p_row02_traceSegment_031_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1296 27 27, g32p_row02_traceSegment_031_1296_0027, g32p_row02_traceSegment_031_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1350 13 14, g32p_row02_traceSegment_031_1350_0013, g32p_row02_traceSegment_031_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1377 13 14, g32p_row02_traceSegment_031_1377_0013, g32p_row02_traceSegment_031_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1350 27 27, g32p_row02_traceSegment_031_1350_0027, g32p_row02_traceSegment_031_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1296 54 54, g32p_row02_traceSegment_031_1296_0054, g32p_row02_traceSegment_031_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1404 13 14, g32p_row02_traceSegment_031_1404_0013, g32p_row02_traceSegment_031_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1431 13 14, g32p_row02_traceSegment_031_1431_0013, g32p_row02_traceSegment_031_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1404 27 27, g32p_row02_traceSegment_031_1404_0027, g32p_row02_traceSegment_031_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1458 13 14, g32p_row02_traceSegment_031_1458_0013, g32p_row02_traceSegment_031_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1485 13 14, g32p_row02_traceSegment_031_1485_0013, g32p_row02_traceSegment_031_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1458 27 27, g32p_row02_traceSegment_031_1458_0027, g32p_row02_traceSegment_031_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1404 54 54, g32p_row02_traceSegment_031_1404_0054, g32p_row02_traceSegment_031_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1296 108 108, g32p_row02_traceSegment_031_1296_0108, g32p_row02_traceSegment_031_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1512 13 14, g32p_row02_traceSegment_031_1512_0013, g32p_row02_traceSegment_031_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1539 13 14, g32p_row02_traceSegment_031_1539_0013, g32p_row02_traceSegment_031_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1512 27 27, g32p_row02_traceSegment_031_1512_0027, g32p_row02_traceSegment_031_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1566 13 14, g32p_row02_traceSegment_031_1566_0013, g32p_row02_traceSegment_031_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1593 13 14, g32p_row02_traceSegment_031_1593_0013, g32p_row02_traceSegment_031_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1566 27 27, g32p_row02_traceSegment_031_1566_0027, g32p_row02_traceSegment_031_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1512 54 54, g32p_row02_traceSegment_031_1512_0054, g32p_row02_traceSegment_031_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1620 13 14, g32p_row02_traceSegment_031_1620_0013, g32p_row02_traceSegment_031_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1647 13 14, g32p_row02_traceSegment_031_1647_0013, g32p_row02_traceSegment_031_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1620 27 27, g32p_row02_traceSegment_031_1620_0027, g32p_row02_traceSegment_031_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1674 13 14, g32p_row02_traceSegment_031_1674_0013, g32p_row02_traceSegment_031_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1701 13 14, g32p_row02_traceSegment_031_1701_0013, g32p_row02_traceSegment_031_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1674 27 27, g32p_row02_traceSegment_031_1674_0027, g32p_row02_traceSegment_031_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1620 54 54, g32p_row02_traceSegment_031_1620_0054, g32p_row02_traceSegment_031_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1512 108 108, g32p_row02_traceSegment_031_1512_0108, g32p_row02_traceSegment_031_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 1296 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1296 216 216, g32p_row02_traceSegment_031_1296_0216, g32p_row02_traceSegment_031_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_031 864 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 864 432 432, g32p_row02_traceSegment_031_0864_0432, g32p_row02_traceSegment_031_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_031 0 1728 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 864 864, g32p_row02_traceSegment_031_0000_0864, g32p_row02_traceSegment_031_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1728 13 14, g32p_row02_traceSegment_031_1728_0013, g32p_row02_traceSegment_031_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1755 13 14, g32p_row02_traceSegment_031_1755_0013, g32p_row02_traceSegment_031_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1728 27 27, g32p_row02_traceSegment_031_1728_0027, g32p_row02_traceSegment_031_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1782 13 14, g32p_row02_traceSegment_031_1782_0013, g32p_row02_traceSegment_031_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1809 13 14, g32p_row02_traceSegment_031_1809_0013, g32p_row02_traceSegment_031_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1782 27 27, g32p_row02_traceSegment_031_1782_0027, g32p_row02_traceSegment_031_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1728 54 54, g32p_row02_traceSegment_031_1728_0054, g32p_row02_traceSegment_031_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1836 13 14, g32p_row02_traceSegment_031_1836_0013, g32p_row02_traceSegment_031_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1863 13 14, g32p_row02_traceSegment_031_1863_0013, g32p_row02_traceSegment_031_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1836 27 27, g32p_row02_traceSegment_031_1836_0027, g32p_row02_traceSegment_031_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1890 13 14, g32p_row02_traceSegment_031_1890_0013, g32p_row02_traceSegment_031_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1917 13 14, g32p_row02_traceSegment_031_1917_0013, g32p_row02_traceSegment_031_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1890 27 27, g32p_row02_traceSegment_031_1890_0027, g32p_row02_traceSegment_031_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1836 54 54, g32p_row02_traceSegment_031_1836_0054, g32p_row02_traceSegment_031_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1728 108 108, g32p_row02_traceSegment_031_1728_0108, g32p_row02_traceSegment_031_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1944 13 14, g32p_row02_traceSegment_031_1944_0013, g32p_row02_traceSegment_031_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1971 13 14, g32p_row02_traceSegment_031_1971_0013, g32p_row02_traceSegment_031_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1944 27 27, g32p_row02_traceSegment_031_1944_0027, g32p_row02_traceSegment_031_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1998 13 14, g32p_row02_traceSegment_031_1998_0013, g32p_row02_traceSegment_031_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2025 13 14, g32p_row02_traceSegment_031_2025_0013, g32p_row02_traceSegment_031_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1998 27 27, g32p_row02_traceSegment_031_1998_0027, g32p_row02_traceSegment_031_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1944 54 54, g32p_row02_traceSegment_031_1944_0054, g32p_row02_traceSegment_031_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2052 13 14, g32p_row02_traceSegment_031_2052_0013, g32p_row02_traceSegment_031_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2079 13 14, g32p_row02_traceSegment_031_2079_0013, g32p_row02_traceSegment_031_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2052 27 27, g32p_row02_traceSegment_031_2052_0027, g32p_row02_traceSegment_031_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2106 13 14, g32p_row02_traceSegment_031_2106_0013, g32p_row02_traceSegment_031_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2133 13 14, g32p_row02_traceSegment_031_2133_0013, g32p_row02_traceSegment_031_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2106 27 27, g32p_row02_traceSegment_031_2106_0027, g32p_row02_traceSegment_031_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2052 54 54, g32p_row02_traceSegment_031_2052_0054, g32p_row02_traceSegment_031_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1944 108 108, g32p_row02_traceSegment_031_1944_0108, g32p_row02_traceSegment_031_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1728 216 216, g32p_row02_traceSegment_031_1728_0216, g32p_row02_traceSegment_031_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2160 13 14, g32p_row02_traceSegment_031_2160_0013, g32p_row02_traceSegment_031_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2187 13 14, g32p_row02_traceSegment_031_2187_0013, g32p_row02_traceSegment_031_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2160 27 27, g32p_row02_traceSegment_031_2160_0027, g32p_row02_traceSegment_031_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2214 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2214 13 14, g32p_row02_traceSegment_031_2214_0013, g32p_row02_traceSegment_031_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2241 13 14, g32p_row02_traceSegment_031_2241_0013, g32p_row02_traceSegment_031_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2214 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2214 27 27, g32p_row02_traceSegment_031_2214_0027, g32p_row02_traceSegment_031_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2160 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2160 54 54, g32p_row02_traceSegment_031_2160_0054, g32p_row02_traceSegment_031_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2268 13 14, g32p_row02_traceSegment_031_2268_0013, g32p_row02_traceSegment_031_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2295 13 14, g32p_row02_traceSegment_031_2295_0013, g32p_row02_traceSegment_031_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2268 27 27, g32p_row02_traceSegment_031_2268_0027, g32p_row02_traceSegment_031_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2322 13 14, g32p_row02_traceSegment_031_2322_0013, g32p_row02_traceSegment_031_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2349 13 14, g32p_row02_traceSegment_031_2349_0013, g32p_row02_traceSegment_031_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2322 27 27, g32p_row02_traceSegment_031_2322_0027, g32p_row02_traceSegment_031_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2268 54 54, g32p_row02_traceSegment_031_2268_0054, g32p_row02_traceSegment_031_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 2160 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2160 108 108, g32p_row02_traceSegment_031_2160_0108, g32p_row02_traceSegment_031_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2376 13 14, g32p_row02_traceSegment_031_2376_0013, g32p_row02_traceSegment_031_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2403 13 14, g32p_row02_traceSegment_031_2403_0013, g32p_row02_traceSegment_031_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2376 27 27, g32p_row02_traceSegment_031_2376_0027, g32p_row02_traceSegment_031_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2430 13 14, g32p_row02_traceSegment_031_2430_0013, g32p_row02_traceSegment_031_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2457 13 14, g32p_row02_traceSegment_031_2457_0013, g32p_row02_traceSegment_031_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2430 27 27, g32p_row02_traceSegment_031_2430_0027, g32p_row02_traceSegment_031_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2376 54 54, g32p_row02_traceSegment_031_2376_0054, g32p_row02_traceSegment_031_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2484 13 14, g32p_row02_traceSegment_031_2484_0013, g32p_row02_traceSegment_031_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2511 13 14, g32p_row02_traceSegment_031_2511_0013, g32p_row02_traceSegment_031_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2484 27 27, g32p_row02_traceSegment_031_2484_0027, g32p_row02_traceSegment_031_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2538 13 14, g32p_row02_traceSegment_031_2538_0013, g32p_row02_traceSegment_031_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2565 13 14, g32p_row02_traceSegment_031_2565_0013, g32p_row02_traceSegment_031_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2538 27 27, g32p_row02_traceSegment_031_2538_0027, g32p_row02_traceSegment_031_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2484 54 54, g32p_row02_traceSegment_031_2484_0054, g32p_row02_traceSegment_031_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2376 108 108, g32p_row02_traceSegment_031_2376_0108, g32p_row02_traceSegment_031_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 2160 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2160 216 216, g32p_row02_traceSegment_031_2160_0216, g32p_row02_traceSegment_031_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 864 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1728 432 432, g32p_row02_traceSegment_031_1728_0432, g32p_row02_traceSegment_031_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2605 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2592 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2592 13 14, g32p_row02_traceSegment_031_2592_0013, g32p_row02_traceSegment_031_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2619 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2632 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2619 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2619 13 14, g32p_row02_traceSegment_031_2619_0013, g32p_row02_traceSegment_031_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2592 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2592 27 27, g32p_row02_traceSegment_031_2592_0027, g32p_row02_traceSegment_031_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2646 13 14, g32p_row02_traceSegment_031_2646_0013, g32p_row02_traceSegment_031_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2673 13 14, g32p_row02_traceSegment_031_2673_0013, g32p_row02_traceSegment_031_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2646 27 27, g32p_row02_traceSegment_031_2646_0027, g32p_row02_traceSegment_031_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2592 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2592 54 54, g32p_row02_traceSegment_031_2592_0054, g32p_row02_traceSegment_031_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2700 13 14, g32p_row02_traceSegment_031_2700_0013, g32p_row02_traceSegment_031_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2727 13 14, g32p_row02_traceSegment_031_2727_0013, g32p_row02_traceSegment_031_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2700 27 27, g32p_row02_traceSegment_031_2700_0027, g32p_row02_traceSegment_031_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2754 13 14, g32p_row02_traceSegment_031_2754_0013, g32p_row02_traceSegment_031_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2781 13 14, g32p_row02_traceSegment_031_2781_0013, g32p_row02_traceSegment_031_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2754 27 27, g32p_row02_traceSegment_031_2754_0027, g32p_row02_traceSegment_031_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2700 54 54, g32p_row02_traceSegment_031_2700_0054, g32p_row02_traceSegment_031_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 2592 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2592 108 108, g32p_row02_traceSegment_031_2592_0108, g32p_row02_traceSegment_031_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2808 13 14, g32p_row02_traceSegment_031_2808_0013, g32p_row02_traceSegment_031_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2848 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2835 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2835 13 14, g32p_row02_traceSegment_031_2835_0013, g32p_row02_traceSegment_031_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2808 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2808 27 27, g32p_row02_traceSegment_031_2808_0027, g32p_row02_traceSegment_031_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2862 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2862 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2862 13 14, g32p_row02_traceSegment_031_2862_0013, g32p_row02_traceSegment_031_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2889 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2889 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2889 13 14, g32p_row02_traceSegment_031_2889_0013, g32p_row02_traceSegment_031_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2862 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2862 27 27, g32p_row02_traceSegment_031_2862_0027, g32p_row02_traceSegment_031_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2808 108 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2808 54 54, g32p_row02_traceSegment_031_2808_0054, g32p_row02_traceSegment_031_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2929 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2916 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2916 13 14, g32p_row02_traceSegment_031_2916_0013, g32p_row02_traceSegment_031_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2943 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2943 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2943 13 14, g32p_row02_traceSegment_031_2943_0013, g32p_row02_traceSegment_031_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2916 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2916 27 27, g32p_row02_traceSegment_031_2916_0027, g32p_row02_traceSegment_031_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2970 13 14, g32p_row02_traceSegment_031_2970_0013, g32p_row02_traceSegment_031_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2997 13 14, g32p_row02_traceSegment_031_2997_0013, g32p_row02_traceSegment_031_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2970 27 27, g32p_row02_traceSegment_031_2970_0027, g32p_row02_traceSegment_031_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 2916 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2916 54 54, g32p_row02_traceSegment_031_2916_0054, g32p_row02_traceSegment_031_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 2808 216 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2808 108 108, g32p_row02_traceSegment_031_2808_0108, g32p_row02_traceSegment_031_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 2592 432 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2592 216 216, g32p_row02_traceSegment_031_2592_0216, g32p_row02_traceSegment_031_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3024 13 14, g32p_row02_traceSegment_031_3024_0013, g32p_row02_traceSegment_031_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3051 13 14, g32p_row02_traceSegment_031_3051_0013, g32p_row02_traceSegment_031_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3024 27 27, g32p_row02_traceSegment_031_3024_0027, g32p_row02_traceSegment_031_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3078 13 14, g32p_row02_traceSegment_031_3078_0013, g32p_row02_traceSegment_031_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3105 13 14, g32p_row02_traceSegment_031_3105_0013, g32p_row02_traceSegment_031_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3078 27 27, g32p_row02_traceSegment_031_3078_0027, g32p_row02_traceSegment_031_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3024 54 54, g32p_row02_traceSegment_031_3024_0054, g32p_row02_traceSegment_031_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3132 13 14, g32p_row02_traceSegment_031_3132_0013, g32p_row02_traceSegment_031_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3159 13 14, g32p_row02_traceSegment_031_3159_0013, g32p_row02_traceSegment_031_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3132 27 27, g32p_row02_traceSegment_031_3132_0027, g32p_row02_traceSegment_031_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3186 13 14, g32p_row02_traceSegment_031_3186_0013, g32p_row02_traceSegment_031_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3213 13 14, g32p_row02_traceSegment_031_3213_0013, g32p_row02_traceSegment_031_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3186 27 27, g32p_row02_traceSegment_031_3186_0027, g32p_row02_traceSegment_031_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3132 54 54, g32p_row02_traceSegment_031_3132_0054, g32p_row02_traceSegment_031_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3024 108 108, g32p_row02_traceSegment_031_3024_0108, g32p_row02_traceSegment_031_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3240 13 14, g32p_row02_traceSegment_031_3240_0013, g32p_row02_traceSegment_031_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3267 13 14, g32p_row02_traceSegment_031_3267_0013, g32p_row02_traceSegment_031_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3240 27 27, g32p_row02_traceSegment_031_3240_0027, g32p_row02_traceSegment_031_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3294 13 14, g32p_row02_traceSegment_031_3294_0013, g32p_row02_traceSegment_031_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3321 13 14, g32p_row02_traceSegment_031_3321_0013, g32p_row02_traceSegment_031_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3294 27 27, g32p_row02_traceSegment_031_3294_0027, g32p_row02_traceSegment_031_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3240 54 54, g32p_row02_traceSegment_031_3240_0054, g32p_row02_traceSegment_031_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3348 13 14, g32p_row02_traceSegment_031_3348_0013, g32p_row02_traceSegment_031_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3375 13 14, g32p_row02_traceSegment_031_3375_0013, g32p_row02_traceSegment_031_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3348 27 27, g32p_row02_traceSegment_031_3348_0027, g32p_row02_traceSegment_031_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3402 13 14, g32p_row02_traceSegment_031_3402_0013, g32p_row02_traceSegment_031_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_031 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_031 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_031_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_031 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3429 13 14, g32p_row02_traceSegment_031_3429_0013, g32p_row02_traceSegment_031_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_031 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3402 27 27, g32p_row02_traceSegment_031_3402_0027, g32p_row02_traceSegment_031_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_031 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3348 54 54, g32p_row02_traceSegment_031_3348_0054, g32p_row02_traceSegment_031_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_031 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3240 108 108, g32p_row02_traceSegment_031_3240_0108, g32p_row02_traceSegment_031_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_031_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_031 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 3024 216 216, g32p_row02_traceSegment_031_3024_0216, g32p_row02_traceSegment_031_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_031_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_031 2592 864 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 2592 432 432, g32p_row02_traceSegment_031_2592_0432, g32p_row02_traceSegment_031_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_031_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_031 1728 1728 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 1728 864 864, g32p_row02_traceSegment_031_1728_0864, g32p_row02_traceSegment_031_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_031_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_031 0 3456 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_031 0 1728 1728, g32p_row02_traceSegment_031_0000_1728, g32p_row02_traceSegment_031_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_031 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 31 = [0, 0, 0, 0, 12] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_031_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_032 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 32 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_032_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 0 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 13 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 0 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 13 14, g32p_row02_traceSegment_032_0000_0013, g32p_row02_traceSegment_032_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 27 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 27 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 27 13 14, g32p_row02_traceSegment_032_0027_0013, g32p_row02_traceSegment_032_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 0 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 27 27, g32p_row02_traceSegment_032_0000_0027, g32p_row02_traceSegment_032_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 67 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 54 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 54 13 14, g32p_row02_traceSegment_032_0054_0013, g32p_row02_traceSegment_032_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 81 13 14, g32p_row02_traceSegment_032_0081_0013, g32p_row02_traceSegment_032_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 54 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 54 27 27, g32p_row02_traceSegment_032_0054_0027, g32p_row02_traceSegment_032_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 0 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 54 54, g32p_row02_traceSegment_032_0000_0054, g32p_row02_traceSegment_032_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 108 13 14, g32p_row02_traceSegment_032_0108_0013, g32p_row02_traceSegment_032_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 135 13 14, g32p_row02_traceSegment_032_0135_0013, g32p_row02_traceSegment_032_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 108 27 27, g32p_row02_traceSegment_032_0108_0027, g32p_row02_traceSegment_032_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 175 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 162 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 162 13 14, g32p_row02_traceSegment_032_0162_0013, g32p_row02_traceSegment_032_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 189 13 14, g32p_row02_traceSegment_032_0189_0013, g32p_row02_traceSegment_032_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 162 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 162 27 27, g32p_row02_traceSegment_032_0162_0027, g32p_row02_traceSegment_032_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 108 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 108 54 54, g32p_row02_traceSegment_032_0108_0054, g32p_row02_traceSegment_032_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 0 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 108 108, g32p_row02_traceSegment_032_0000_0108, g32p_row02_traceSegment_032_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 216 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 216 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 216 13 14, g32p_row02_traceSegment_032_0216_0013, g32p_row02_traceSegment_032_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 243 13 14, g32p_row02_traceSegment_032_0243_0013, g32p_row02_traceSegment_032_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 216 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 216 27 27, g32p_row02_traceSegment_032_0216_0027, g32p_row02_traceSegment_032_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 270 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 270 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 270 13 14, g32p_row02_traceSegment_032_0270_0013, g32p_row02_traceSegment_032_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 297 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 297 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 297 13 14, g32p_row02_traceSegment_032_0297_0013, g32p_row02_traceSegment_032_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 270 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 270 27 27, g32p_row02_traceSegment_032_0270_0027, g32p_row02_traceSegment_032_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 216 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 216 54 54, g32p_row02_traceSegment_032_0216_0054, g32p_row02_traceSegment_032_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 324 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 337 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 324 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 324 13 14, g32p_row02_traceSegment_032_0324_0013, g32p_row02_traceSegment_032_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 351 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 364 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 351 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 351 13 14, g32p_row02_traceSegment_032_0351_0013, g32p_row02_traceSegment_032_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 324 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 324 27 27, g32p_row02_traceSegment_032_0324_0027, g32p_row02_traceSegment_032_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 378 13 14, g32p_row02_traceSegment_032_0378_0013, g32p_row02_traceSegment_032_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 405 13 14, g32p_row02_traceSegment_032_0405_0013, g32p_row02_traceSegment_032_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 378 27 27, g32p_row02_traceSegment_032_0378_0027, g32p_row02_traceSegment_032_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 324 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 324 54 54, g32p_row02_traceSegment_032_0324_0054, g32p_row02_traceSegment_032_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 216 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 216 108 108, g32p_row02_traceSegment_032_0216_0108, g32p_row02_traceSegment_032_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 0 432 = [0, 0, 0, 0, 12] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 216 216, g32p_row02_traceSegment_032_0000_0216, g32p_row02_traceSegment_032_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 432 13 14, g32p_row02_traceSegment_032_0432_0013, g32p_row02_traceSegment_032_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 459 13 14, g32p_row02_traceSegment_032_0459_0013, g32p_row02_traceSegment_032_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 432 27 27, g32p_row02_traceSegment_032_0432_0027, g32p_row02_traceSegment_032_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 486 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 499 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 486 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 486 13 14, g32p_row02_traceSegment_032_0486_0013, g32p_row02_traceSegment_032_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 513 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 513 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 513 13 14, g32p_row02_traceSegment_032_0513_0013, g32p_row02_traceSegment_032_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 486 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 486 27 27, g32p_row02_traceSegment_032_0486_0027, g32p_row02_traceSegment_032_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 432 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 432 54 54, g32p_row02_traceSegment_032_0432_0054, g32p_row02_traceSegment_032_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 540 13 14, g32p_row02_traceSegment_032_0540_0013, g32p_row02_traceSegment_032_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 567 13 14, g32p_row02_traceSegment_032_0567_0013, g32p_row02_traceSegment_032_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 540 27 27, g32p_row02_traceSegment_032_0540_0027, g32p_row02_traceSegment_032_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 594 13 14, g32p_row02_traceSegment_032_0594_0013, g32p_row02_traceSegment_032_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 621 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 634 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 621 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 621 13 14, g32p_row02_traceSegment_032_0621_0013, g32p_row02_traceSegment_032_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 594 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 594 27 27, g32p_row02_traceSegment_032_0594_0027, g32p_row02_traceSegment_032_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 540 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 540 54 54, g32p_row02_traceSegment_032_0540_0054, g32p_row02_traceSegment_032_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 432 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 432 108 108, g32p_row02_traceSegment_032_0432_0108, g32p_row02_traceSegment_032_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 648 13 14, g32p_row02_traceSegment_032_0648_0013, g32p_row02_traceSegment_032_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 675 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 675 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 675 13 14, g32p_row02_traceSegment_032_0675_0013, g32p_row02_traceSegment_032_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 648 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 648 27 27, g32p_row02_traceSegment_032_0648_0027, g32p_row02_traceSegment_032_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 715 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 702 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 702 13 14, g32p_row02_traceSegment_032_0702_0013, g32p_row02_traceSegment_032_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 729 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 729 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 729 13 14, g32p_row02_traceSegment_032_0729_0013, g32p_row02_traceSegment_032_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 702 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 702 27 27, g32p_row02_traceSegment_032_0702_0027, g32p_row02_traceSegment_032_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 648 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 648 54 54, g32p_row02_traceSegment_032_0648_0054, g32p_row02_traceSegment_032_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 756 13 14, g32p_row02_traceSegment_032_0756_0013, g32p_row02_traceSegment_032_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 783 13 14, g32p_row02_traceSegment_032_0783_0013, g32p_row02_traceSegment_032_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 756 27 27, g32p_row02_traceSegment_032_0756_0027, g32p_row02_traceSegment_032_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 810 13 14, g32p_row02_traceSegment_032_0810_0013, g32p_row02_traceSegment_032_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 837 13 14, g32p_row02_traceSegment_032_0837_0013, g32p_row02_traceSegment_032_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 810 27 27, g32p_row02_traceSegment_032_0810_0027, g32p_row02_traceSegment_032_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 756 54 54, g32p_row02_traceSegment_032_0756_0054, g32p_row02_traceSegment_032_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 648 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 648 108 108, g32p_row02_traceSegment_032_0648_0108, g32p_row02_traceSegment_032_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 432 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 432 216 216, g32p_row02_traceSegment_032_0432_0216, g32p_row02_traceSegment_032_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_032 0 864 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 432 432, g32p_row02_traceSegment_032_0000_0432, g32p_row02_traceSegment_032_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 877 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 864 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 864 13 14, g32p_row02_traceSegment_032_0864_0013, g32p_row02_traceSegment_032_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 891 13 14, g32p_row02_traceSegment_032_0891_0013, g32p_row02_traceSegment_032_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 864 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 864 27 27, g32p_row02_traceSegment_032_0864_0027, g32p_row02_traceSegment_032_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 918 13 14, g32p_row02_traceSegment_032_0918_0013, g32p_row02_traceSegment_032_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 945 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 958 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 945 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 945 13 14, g32p_row02_traceSegment_032_0945_0013, g32p_row02_traceSegment_032_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 918 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 918 27 27, g32p_row02_traceSegment_032_0918_0027, g32p_row02_traceSegment_032_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 864 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 864 54 54, g32p_row02_traceSegment_032_0864_0054, g32p_row02_traceSegment_032_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 972 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 985 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 972 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 972 13 14, g32p_row02_traceSegment_032_0972_0013, g32p_row02_traceSegment_032_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1012 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 999 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 999 13 14, g32p_row02_traceSegment_032_0999_0013, g32p_row02_traceSegment_032_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 972 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 972 27 27, g32p_row02_traceSegment_032_0972_0027, g32p_row02_traceSegment_032_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1039 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1026 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1026 13 14, g32p_row02_traceSegment_032_1026_0013, g32p_row02_traceSegment_032_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1053 13 14, g32p_row02_traceSegment_032_1053_0013, g32p_row02_traceSegment_032_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1026 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1026 27 27, g32p_row02_traceSegment_032_1026_0027, g32p_row02_traceSegment_032_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 972 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 972 54 54, g32p_row02_traceSegment_032_0972_0054, g32p_row02_traceSegment_032_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 864 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 864 108 108, g32p_row02_traceSegment_032_0864_0108, g32p_row02_traceSegment_032_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1093 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1080 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1080 13 14, g32p_row02_traceSegment_032_1080_0013, g32p_row02_traceSegment_032_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1107 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1107 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1107 13 14, g32p_row02_traceSegment_032_1107_0013, g32p_row02_traceSegment_032_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1080 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1080 27 27, g32p_row02_traceSegment_032_1080_0027, g32p_row02_traceSegment_032_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1134 13 14, g32p_row02_traceSegment_032_1134_0013, g32p_row02_traceSegment_032_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1174 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1161 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1161 13 14, g32p_row02_traceSegment_032_1161_0013, g32p_row02_traceSegment_032_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1134 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1134 27 27, g32p_row02_traceSegment_032_1134_0027, g32p_row02_traceSegment_032_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1080 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1080 54 54, g32p_row02_traceSegment_032_1080_0054, g32p_row02_traceSegment_032_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1188 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1188 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1188 13 14, g32p_row02_traceSegment_032_1188_0013, g32p_row02_traceSegment_032_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1215 13 14, g32p_row02_traceSegment_032_1215_0013, g32p_row02_traceSegment_032_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1188 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1188 27 27, g32p_row02_traceSegment_032_1188_0027, g32p_row02_traceSegment_032_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1242 13 14, g32p_row02_traceSegment_032_1242_0013, g32p_row02_traceSegment_032_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1269 13 14, g32p_row02_traceSegment_032_1269_0013, g32p_row02_traceSegment_032_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1242 27 27, g32p_row02_traceSegment_032_1242_0027, g32p_row02_traceSegment_032_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1188 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1188 54 54, g32p_row02_traceSegment_032_1188_0054, g32p_row02_traceSegment_032_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 1080 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1080 108 108, g32p_row02_traceSegment_032_1080_0108, g32p_row02_traceSegment_032_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 864 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 864 216 216, g32p_row02_traceSegment_032_0864_0216, g32p_row02_traceSegment_032_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1296 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1296 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1296 13 14, g32p_row02_traceSegment_032_1296_0013, g32p_row02_traceSegment_032_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1336 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1323 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1323 13 14, g32p_row02_traceSegment_032_1323_0013, g32p_row02_traceSegment_032_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1296 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1296 27 27, g32p_row02_traceSegment_032_1296_0027, g32p_row02_traceSegment_032_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1350 13 14, g32p_row02_traceSegment_032_1350_0013, g32p_row02_traceSegment_032_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1390 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1377 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1377 13 14, g32p_row02_traceSegment_032_1377_0013, g32p_row02_traceSegment_032_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1350 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1350 27 27, g32p_row02_traceSegment_032_1350_0027, g32p_row02_traceSegment_032_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1296 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1296 54 54, g32p_row02_traceSegment_032_1296_0054, g32p_row02_traceSegment_032_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1404 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1404 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1404 13 14, g32p_row02_traceSegment_032_1404_0013, g32p_row02_traceSegment_032_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1444 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1431 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1431 13 14, g32p_row02_traceSegment_032_1431_0013, g32p_row02_traceSegment_032_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1404 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1404 27 27, g32p_row02_traceSegment_032_1404_0027, g32p_row02_traceSegment_032_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1458 13 14, g32p_row02_traceSegment_032_1458_0013, g32p_row02_traceSegment_032_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1485 13 14, g32p_row02_traceSegment_032_1485_0013, g32p_row02_traceSegment_032_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1458 27 27, g32p_row02_traceSegment_032_1458_0027, g32p_row02_traceSegment_032_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1404 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1404 54 54, g32p_row02_traceSegment_032_1404_0054, g32p_row02_traceSegment_032_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 1296 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1296 108 108, g32p_row02_traceSegment_032_1296_0108, g32p_row02_traceSegment_032_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1512 13 14, g32p_row02_traceSegment_032_1512_0013, g32p_row02_traceSegment_032_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1539 13 14, g32p_row02_traceSegment_032_1539_0013, g32p_row02_traceSegment_032_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1512 27 27, g32p_row02_traceSegment_032_1512_0027, g32p_row02_traceSegment_032_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1579 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1566 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1566 13 14, g32p_row02_traceSegment_032_1566_0013, g32p_row02_traceSegment_032_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1593 13 14, g32p_row02_traceSegment_032_1593_0013, g32p_row02_traceSegment_032_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1566 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1566 27 27, g32p_row02_traceSegment_032_1566_0027, g32p_row02_traceSegment_032_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1512 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1512 54 54, g32p_row02_traceSegment_032_1512_0054, g32p_row02_traceSegment_032_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1620 13 14, g32p_row02_traceSegment_032_1620_0013, g32p_row02_traceSegment_032_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1647 13 14, g32p_row02_traceSegment_032_1647_0013, g32p_row02_traceSegment_032_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1620 27 27, g32p_row02_traceSegment_032_1620_0027, g32p_row02_traceSegment_032_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1674 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1687 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1674 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1674 13 14, g32p_row02_traceSegment_032_1674_0013, g32p_row02_traceSegment_032_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1701 13 14, g32p_row02_traceSegment_032_1701_0013, g32p_row02_traceSegment_032_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1674 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1674 27 27, g32p_row02_traceSegment_032_1674_0027, g32p_row02_traceSegment_032_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1620 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1620 54 54, g32p_row02_traceSegment_032_1620_0054, g32p_row02_traceSegment_032_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 1512 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1512 108 108, g32p_row02_traceSegment_032_1512_0108, g32p_row02_traceSegment_032_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 1296 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1296 216 216, g32p_row02_traceSegment_032_1296_0216, g32p_row02_traceSegment_032_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_032 864 864 = [0, 0, 0, 0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 864 432 432, g32p_row02_traceSegment_032_0864_0432, g32p_row02_traceSegment_032_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_032 0 1728 = [0, 0, 0, 0, 24] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 864 864, g32p_row02_traceSegment_032_0000_0864, g32p_row02_traceSegment_032_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1728 13 14, g32p_row02_traceSegment_032_1728_0013, g32p_row02_traceSegment_032_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1755 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1768 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1755 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1755 13 14, g32p_row02_traceSegment_032_1755_0013, g32p_row02_traceSegment_032_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1728 27 27, g32p_row02_traceSegment_032_1728_0027, g32p_row02_traceSegment_032_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1782 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1782 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1782 13 14, g32p_row02_traceSegment_032_1782_0013, g32p_row02_traceSegment_032_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1809 13 14, g32p_row02_traceSegment_032_1809_0013, g32p_row02_traceSegment_032_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1782 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1782 27 27, g32p_row02_traceSegment_032_1782_0027, g32p_row02_traceSegment_032_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1728 54 54, g32p_row02_traceSegment_032_1728_0054, g32p_row02_traceSegment_032_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1849 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1836 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1836 13 14, g32p_row02_traceSegment_032_1836_0013, g32p_row02_traceSegment_032_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1863 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1876 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1863 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1863 13 14, g32p_row02_traceSegment_032_1863_0013, g32p_row02_traceSegment_032_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1836 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1836 27 27, g32p_row02_traceSegment_032_1836_0027, g32p_row02_traceSegment_032_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1890 13 14, g32p_row02_traceSegment_032_1890_0013, g32p_row02_traceSegment_032_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1917 13 14, g32p_row02_traceSegment_032_1917_0013, g32p_row02_traceSegment_032_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1890 27 27, g32p_row02_traceSegment_032_1890_0027, g32p_row02_traceSegment_032_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1836 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1836 54 54, g32p_row02_traceSegment_032_1836_0054, g32p_row02_traceSegment_032_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1728 108 108, g32p_row02_traceSegment_032_1728_0108, g32p_row02_traceSegment_032_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1944 13 14, g32p_row02_traceSegment_032_1944_0013, g32p_row02_traceSegment_032_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1971 13 14, g32p_row02_traceSegment_032_1971_0013, g32p_row02_traceSegment_032_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1944 27 27, g32p_row02_traceSegment_032_1944_0027, g32p_row02_traceSegment_032_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1998 13 14, g32p_row02_traceSegment_032_1998_0013, g32p_row02_traceSegment_032_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2025 13 14, g32p_row02_traceSegment_032_2025_0013, g32p_row02_traceSegment_032_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1998 27 27, g32p_row02_traceSegment_032_1998_0027, g32p_row02_traceSegment_032_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1944 54 54, g32p_row02_traceSegment_032_1944_0054, g32p_row02_traceSegment_032_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2052 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2065 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2052 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2052 13 14, g32p_row02_traceSegment_032_2052_0013, g32p_row02_traceSegment_032_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2079 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2092 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2079 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2079 13 14, g32p_row02_traceSegment_032_2079_0013, g32p_row02_traceSegment_032_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2052 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2052 27 27, g32p_row02_traceSegment_032_2052_0027, g32p_row02_traceSegment_032_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2106 13 14, g32p_row02_traceSegment_032_2106_0013, g32p_row02_traceSegment_032_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2133 13 14, g32p_row02_traceSegment_032_2133_0013, g32p_row02_traceSegment_032_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2106 27 27, g32p_row02_traceSegment_032_2106_0027, g32p_row02_traceSegment_032_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2052 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2052 54 54, g32p_row02_traceSegment_032_2052_0054, g32p_row02_traceSegment_032_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 1944 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1944 108 108, g32p_row02_traceSegment_032_1944_0108, g32p_row02_traceSegment_032_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1728 216 216, g32p_row02_traceSegment_032_1728_0216, g32p_row02_traceSegment_032_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2173 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2160 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2160 13 14, g32p_row02_traceSegment_032_2160_0013, g32p_row02_traceSegment_032_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2187 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2200 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2187 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2187 13 14, g32p_row02_traceSegment_032_2187_0013, g32p_row02_traceSegment_032_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2160 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2160 27 27, g32p_row02_traceSegment_032_2160_0027, g32p_row02_traceSegment_032_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2214 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2227 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2214 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2214 13 14, g32p_row02_traceSegment_032_2214_0013, g32p_row02_traceSegment_032_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2254 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2241 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2241 13 14, g32p_row02_traceSegment_032_2241_0013, g32p_row02_traceSegment_032_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2214 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2214 27 27, g32p_row02_traceSegment_032_2214_0027, g32p_row02_traceSegment_032_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2160 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2160 54 54, g32p_row02_traceSegment_032_2160_0054, g32p_row02_traceSegment_032_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2268 13 14, g32p_row02_traceSegment_032_2268_0013, g32p_row02_traceSegment_032_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2308 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2295 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2295 13 14, g32p_row02_traceSegment_032_2295_0013, g32p_row02_traceSegment_032_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2268 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2268 27 27, g32p_row02_traceSegment_032_2268_0027, g32p_row02_traceSegment_032_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2335 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2322 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2322 13 14, g32p_row02_traceSegment_032_2322_0013, g32p_row02_traceSegment_032_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2349 13 14, g32p_row02_traceSegment_032_2349_0013, g32p_row02_traceSegment_032_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2322 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2322 27 27, g32p_row02_traceSegment_032_2322_0027, g32p_row02_traceSegment_032_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2268 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2268 54 54, g32p_row02_traceSegment_032_2268_0054, g32p_row02_traceSegment_032_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 2160 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2160 108 108, g32p_row02_traceSegment_032_2160_0108, g32p_row02_traceSegment_032_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2376 13 14, g32p_row02_traceSegment_032_2376_0013, g32p_row02_traceSegment_032_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2403 13 14, g32p_row02_traceSegment_032_2403_0013, g32p_row02_traceSegment_032_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2376 27 27, g32p_row02_traceSegment_032_2376_0027, g32p_row02_traceSegment_032_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2430 13 14, g32p_row02_traceSegment_032_2430_0013, g32p_row02_traceSegment_032_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2457 13 14, g32p_row02_traceSegment_032_2457_0013, g32p_row02_traceSegment_032_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2430 27 27, g32p_row02_traceSegment_032_2430_0027, g32p_row02_traceSegment_032_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2376 54 54, g32p_row02_traceSegment_032_2376_0054, g32p_row02_traceSegment_032_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2484 13 14, g32p_row02_traceSegment_032_2484_0013, g32p_row02_traceSegment_032_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2511 13 14, g32p_row02_traceSegment_032_2511_0013, g32p_row02_traceSegment_032_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2484 27 27, g32p_row02_traceSegment_032_2484_0027, g32p_row02_traceSegment_032_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2551 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2538 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2538 13 14, g32p_row02_traceSegment_032_2538_0013, g32p_row02_traceSegment_032_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2565 13 14, g32p_row02_traceSegment_032_2565_0013, g32p_row02_traceSegment_032_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2538 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2538 27 27, g32p_row02_traceSegment_032_2538_0027, g32p_row02_traceSegment_032_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2484 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2484 54 54, g32p_row02_traceSegment_032_2484_0054, g32p_row02_traceSegment_032_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 2376 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2376 108 108, g32p_row02_traceSegment_032_2376_0108, g32p_row02_traceSegment_032_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 2160 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2160 216 216, g32p_row02_traceSegment_032_2160_0216, g32p_row02_traceSegment_032_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1728 432 432, g32p_row02_traceSegment_032_1728_0432, g32p_row02_traceSegment_032_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2592 13 14, g32p_row02_traceSegment_032_2592_0013, g32p_row02_traceSegment_032_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2619 13 14, g32p_row02_traceSegment_032_2619_0013, g32p_row02_traceSegment_032_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2592 27 27, g32p_row02_traceSegment_032_2592_0027, g32p_row02_traceSegment_032_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2659 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2646 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2646 13 14, g32p_row02_traceSegment_032_2646_0013, g32p_row02_traceSegment_032_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2686 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2673 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2673 13 14, g32p_row02_traceSegment_032_2673_0013, g32p_row02_traceSegment_032_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2646 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2646 27 27, g32p_row02_traceSegment_032_2646_0027, g32p_row02_traceSegment_032_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2592 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2592 54 54, g32p_row02_traceSegment_032_2592_0054, g32p_row02_traceSegment_032_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2713 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2700 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2700 13 14, g32p_row02_traceSegment_032_2700_0013, g32p_row02_traceSegment_032_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2740 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2727 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2727 13 14, g32p_row02_traceSegment_032_2727_0013, g32p_row02_traceSegment_032_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2700 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2700 27 27, g32p_row02_traceSegment_032_2700_0027, g32p_row02_traceSegment_032_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2754 13 14, g32p_row02_traceSegment_032_2754_0013, g32p_row02_traceSegment_032_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2781 13 14, g32p_row02_traceSegment_032_2781_0013, g32p_row02_traceSegment_032_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2754 27 27, g32p_row02_traceSegment_032_2754_0027, g32p_row02_traceSegment_032_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2700 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2700 54 54, g32p_row02_traceSegment_032_2700_0054, g32p_row02_traceSegment_032_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 2592 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2592 108 108, g32p_row02_traceSegment_032_2592_0108, g32p_row02_traceSegment_032_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2808 13 14, g32p_row02_traceSegment_032_2808_0013, g32p_row02_traceSegment_032_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2835 13 14, g32p_row02_traceSegment_032_2835_0013, g32p_row02_traceSegment_032_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2808 27 27, g32p_row02_traceSegment_032_2808_0027, g32p_row02_traceSegment_032_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2875 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2862 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2862 13 14, g32p_row02_traceSegment_032_2862_0013, g32p_row02_traceSegment_032_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2889 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2902 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2889 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2889 13 14, g32p_row02_traceSegment_032_2889_0013, g32p_row02_traceSegment_032_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2862 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2862 27 27, g32p_row02_traceSegment_032_2862_0027, g32p_row02_traceSegment_032_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2808 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2808 54 54, g32p_row02_traceSegment_032_2808_0054, g32p_row02_traceSegment_032_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2929 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2916 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2916 13 14, g32p_row02_traceSegment_032_2916_0013, g32p_row02_traceSegment_032_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2943 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2956 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2943 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2943 13 14, g32p_row02_traceSegment_032_2943_0013, g32p_row02_traceSegment_032_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2916 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2916 27 27, g32p_row02_traceSegment_032_2916_0027, g32p_row02_traceSegment_032_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 2983 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2970 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2970 13 14, g32p_row02_traceSegment_032_2970_0013, g32p_row02_traceSegment_032_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2997 13 14, g32p_row02_traceSegment_032_2997_0013, g32p_row02_traceSegment_032_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 2970 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2970 27 27, g32p_row02_traceSegment_032_2970_0027, g32p_row02_traceSegment_032_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 2916 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2916 54 54, g32p_row02_traceSegment_032_2916_0054, g32p_row02_traceSegment_032_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 2808 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2808 108 108, g32p_row02_traceSegment_032_2808_0108, g32p_row02_traceSegment_032_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 2592 432 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2592 216 216, g32p_row02_traceSegment_032_2592_0216, g32p_row02_traceSegment_032_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3024 13 14, g32p_row02_traceSegment_032_3024_0013, g32p_row02_traceSegment_032_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3051 13 14, g32p_row02_traceSegment_032_3051_0013, g32p_row02_traceSegment_032_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3024 27 27, g32p_row02_traceSegment_032_3024_0027, g32p_row02_traceSegment_032_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3078 13 14, g32p_row02_traceSegment_032_3078_0013, g32p_row02_traceSegment_032_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3105 13 14, g32p_row02_traceSegment_032_3105_0013, g32p_row02_traceSegment_032_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3078 27 27, g32p_row02_traceSegment_032_3078_0027, g32p_row02_traceSegment_032_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3024 54 54, g32p_row02_traceSegment_032_3024_0054, g32p_row02_traceSegment_032_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3132 13 14, g32p_row02_traceSegment_032_3132_0013, g32p_row02_traceSegment_032_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3159 13 14, g32p_row02_traceSegment_032_3159_0013, g32p_row02_traceSegment_032_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3132 27 27, g32p_row02_traceSegment_032_3132_0027, g32p_row02_traceSegment_032_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3186 13 14, g32p_row02_traceSegment_032_3186_0013, g32p_row02_traceSegment_032_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3213 13 14, g32p_row02_traceSegment_032_3213_0013, g32p_row02_traceSegment_032_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3186 27 27, g32p_row02_traceSegment_032_3186_0027, g32p_row02_traceSegment_032_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3132 54 54, g32p_row02_traceSegment_032_3132_0054, g32p_row02_traceSegment_032_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3024 108 108, g32p_row02_traceSegment_032_3024_0108, g32p_row02_traceSegment_032_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3240 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3240 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3240 13 14, g32p_row02_traceSegment_032_3240_0013, g32p_row02_traceSegment_032_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3267 13 14, g32p_row02_traceSegment_032_3267_0013, g32p_row02_traceSegment_032_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3240 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3240 27 27, g32p_row02_traceSegment_032_3240_0027, g32p_row02_traceSegment_032_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3294 13 14, g32p_row02_traceSegment_032_3294_0013, g32p_row02_traceSegment_032_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3321 13 14, g32p_row02_traceSegment_032_3321_0013, g32p_row02_traceSegment_032_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3294 27 27, g32p_row02_traceSegment_032_3294_0027, g32p_row02_traceSegment_032_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 3240 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3240 54 54, g32p_row02_traceSegment_032_3240_0054, g32p_row02_traceSegment_032_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3361 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3348 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3348 13 14, g32p_row02_traceSegment_032_3348_0013, g32p_row02_traceSegment_032_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3375 13 14, g32p_row02_traceSegment_032_3375_0013, g32p_row02_traceSegment_032_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3348 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3348 27 27, g32p_row02_traceSegment_032_3348_0027, g32p_row02_traceSegment_032_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3402 13 14, g32p_row02_traceSegment_032_3402_0013, g32p_row02_traceSegment_032_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_032 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_032 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_032_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_032 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3429 13 14, g32p_row02_traceSegment_032_3429_0013, g32p_row02_traceSegment_032_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_032 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3402 27 27, g32p_row02_traceSegment_032_3402_0027, g32p_row02_traceSegment_032_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_032 3348 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3348 54 54, g32p_row02_traceSegment_032_3348_0054, g32p_row02_traceSegment_032_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_032 3240 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3240 108 108, g32p_row02_traceSegment_032_3240_0108, g32p_row02_traceSegment_032_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_032_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_032 3024 432 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 3024 216 216, g32p_row02_traceSegment_032_3024_0216, g32p_row02_traceSegment_032_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_032_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_032 2592 864 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 2592 432 432, g32p_row02_traceSegment_032_2592_0432, g32p_row02_traceSegment_032_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_032_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_032 1728 1728 = [0, 0, 0, 0, 8] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 1728 864 864, g32p_row02_traceSegment_032_1728_0864, g32p_row02_traceSegment_032_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_032_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_032 0 3456 = [0, 0, 0, 0, 32] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_032 0 1728 1728, g32p_row02_traceSegment_032_0000_1728, g32p_row02_traceSegment_032_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_032 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 32 = [0, 0, 0, 0, 32] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_032_0000_3456

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

private def g32p_row02_traceSegment_034 (k : ℕ) : List ℤ :=
  if g32p_row02_supplierClassifier (Fin.ofNat 3456 k) = 34 then
    g32p_coeffMonomial (Multiplicative.toAdd (g32p_row02_characterValues (Fin.ofNat 3456 k))).val 1 else []

private theorem g32p_row02_traceSegment_034_0000_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 0 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0013_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 13 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 0 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 13 14, g32p_row02_traceSegment_034_0000_0013, g32p_row02_traceSegment_034_0013_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0027_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 27 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0040_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 40 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0027_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 27 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 27 13 14, g32p_row02_traceSegment_034_0027_0013, g32p_row02_traceSegment_034_0040_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 0 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 27 27, g32p_row02_traceSegment_034_0000_0027, g32p_row02_traceSegment_034_0027_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0054_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 54 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0067_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 67 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0054_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 54 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 54 13 14, g32p_row02_traceSegment_034_0054_0013, g32p_row02_traceSegment_034_0067_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0081_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 81 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0094_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 94 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0081_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 81 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 81 13 14, g32p_row02_traceSegment_034_0081_0013, g32p_row02_traceSegment_034_0094_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0054_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 54 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 54 27 27, g32p_row02_traceSegment_034_0054_0027, g32p_row02_traceSegment_034_0081_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 0 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 54 54, g32p_row02_traceSegment_034_0000_0054, g32p_row02_traceSegment_034_0054_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0108_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 108 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0121_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 121 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0108_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 108 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 108 13 14, g32p_row02_traceSegment_034_0108_0013, g32p_row02_traceSegment_034_0121_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0135_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 135 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0148_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 148 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0135_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 135 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 135 13 14, g32p_row02_traceSegment_034_0135_0013, g32p_row02_traceSegment_034_0148_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0108_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 108 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 108 27 27, g32p_row02_traceSegment_034_0108_0027, g32p_row02_traceSegment_034_0135_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0162_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 162 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0175_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 175 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0162_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 162 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 162 13 14, g32p_row02_traceSegment_034_0162_0013, g32p_row02_traceSegment_034_0175_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0189_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 189 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0202_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 202 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0189_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 189 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 189 13 14, g32p_row02_traceSegment_034_0189_0013, g32p_row02_traceSegment_034_0202_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0162_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 162 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 162 27 27, g32p_row02_traceSegment_034_0162_0027, g32p_row02_traceSegment_034_0189_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0108_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 108 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 108 54 54, g32p_row02_traceSegment_034_0108_0054, g32p_row02_traceSegment_034_0162_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 0 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 108 108, g32p_row02_traceSegment_034_0000_0108, g32p_row02_traceSegment_034_0108_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0216_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 216 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0229_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 229 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0216_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 216 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 216 13 14, g32p_row02_traceSegment_034_0216_0013, g32p_row02_traceSegment_034_0229_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0243_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 243 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0256_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 256 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0243_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 243 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 243 13 14, g32p_row02_traceSegment_034_0243_0013, g32p_row02_traceSegment_034_0256_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0216_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 216 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 216 27 27, g32p_row02_traceSegment_034_0216_0027, g32p_row02_traceSegment_034_0243_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0270_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 270 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0283_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 283 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0270_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 270 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 270 13 14, g32p_row02_traceSegment_034_0270_0013, g32p_row02_traceSegment_034_0283_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0297_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 297 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0310_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 310 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0297_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 297 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 297 13 14, g32p_row02_traceSegment_034_0297_0013, g32p_row02_traceSegment_034_0310_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0270_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 270 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 270 27 27, g32p_row02_traceSegment_034_0270_0027, g32p_row02_traceSegment_034_0297_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0216_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 216 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 216 54 54, g32p_row02_traceSegment_034_0216_0054, g32p_row02_traceSegment_034_0270_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0324_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 324 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0337_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 337 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0324_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 324 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 324 13 14, g32p_row02_traceSegment_034_0324_0013, g32p_row02_traceSegment_034_0337_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0351_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 351 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0364_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 364 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0351_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 351 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 351 13 14, g32p_row02_traceSegment_034_0351_0013, g32p_row02_traceSegment_034_0364_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0324_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 324 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 324 27 27, g32p_row02_traceSegment_034_0324_0027, g32p_row02_traceSegment_034_0351_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0378_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 378 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0391_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 391 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0378_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 378 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 378 13 14, g32p_row02_traceSegment_034_0378_0013, g32p_row02_traceSegment_034_0391_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0405_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 405 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0418_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 418 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0405_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 405 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 405 13 14, g32p_row02_traceSegment_034_0405_0013, g32p_row02_traceSegment_034_0418_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0378_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 378 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 378 27 27, g32p_row02_traceSegment_034_0378_0027, g32p_row02_traceSegment_034_0405_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0324_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 324 108 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 324 54 54, g32p_row02_traceSegment_034_0324_0054, g32p_row02_traceSegment_034_0378_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0216_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 216 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 216 108 108, g32p_row02_traceSegment_034_0216_0108, g32p_row02_traceSegment_034_0324_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 0 432 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 216 216, g32p_row02_traceSegment_034_0000_0216, g32p_row02_traceSegment_034_0216_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0432_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 432 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0445_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 445 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0432_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 432 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 432 13 14, g32p_row02_traceSegment_034_0432_0013, g32p_row02_traceSegment_034_0445_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0459_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 459 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0472_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 472 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0459_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 459 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 459 13 14, g32p_row02_traceSegment_034_0459_0013, g32p_row02_traceSegment_034_0472_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0432_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 432 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 432 27 27, g32p_row02_traceSegment_034_0432_0027, g32p_row02_traceSegment_034_0459_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0486_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 486 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0499_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 499 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0486_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 486 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 486 13 14, g32p_row02_traceSegment_034_0486_0013, g32p_row02_traceSegment_034_0499_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0513_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 513 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0526_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 526 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0513_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 513 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 513 13 14, g32p_row02_traceSegment_034_0513_0013, g32p_row02_traceSegment_034_0526_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0486_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 486 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 486 27 27, g32p_row02_traceSegment_034_0486_0027, g32p_row02_traceSegment_034_0513_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0432_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 432 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 432 54 54, g32p_row02_traceSegment_034_0432_0054, g32p_row02_traceSegment_034_0486_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0540_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 540 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0553_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 553 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0540_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 540 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 540 13 14, g32p_row02_traceSegment_034_0540_0013, g32p_row02_traceSegment_034_0553_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0567_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 567 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0580_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 580 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0567_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 567 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 567 13 14, g32p_row02_traceSegment_034_0567_0013, g32p_row02_traceSegment_034_0580_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0540_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 540 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 540 27 27, g32p_row02_traceSegment_034_0540_0027, g32p_row02_traceSegment_034_0567_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0594_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 594 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0607_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 607 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0594_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 594 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 594 13 14, g32p_row02_traceSegment_034_0594_0013, g32p_row02_traceSegment_034_0607_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0621_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 621 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0634_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 634 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0621_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 621 27 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 621 13 14, g32p_row02_traceSegment_034_0621_0013, g32p_row02_traceSegment_034_0634_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0594_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 594 54 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 594 27 27, g32p_row02_traceSegment_034_0594_0027, g32p_row02_traceSegment_034_0621_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0540_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 540 108 = [0, 0, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 540 54 54, g32p_row02_traceSegment_034_0540_0054, g32p_row02_traceSegment_034_0594_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0432_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 432 216 = [0, 0, 0, 0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 432 108 108, g32p_row02_traceSegment_034_0432_0108, g32p_row02_traceSegment_034_0540_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0648_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 648 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0661_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 661 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0648_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 648 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 648 13 14, g32p_row02_traceSegment_034_0648_0013, g32p_row02_traceSegment_034_0661_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0675_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 675 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0688_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 688 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0675_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 675 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 675 13 14, g32p_row02_traceSegment_034_0675_0013, g32p_row02_traceSegment_034_0688_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0648_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 648 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 648 27 27, g32p_row02_traceSegment_034_0648_0027, g32p_row02_traceSegment_034_0675_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0702_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 702 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0715_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 715 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0702_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 702 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 702 13 14, g32p_row02_traceSegment_034_0702_0013, g32p_row02_traceSegment_034_0715_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0729_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 729 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0742_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 742 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0729_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 729 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 729 13 14, g32p_row02_traceSegment_034_0729_0013, g32p_row02_traceSegment_034_0742_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0702_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 702 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 702 27 27, g32p_row02_traceSegment_034_0702_0027, g32p_row02_traceSegment_034_0729_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0648_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 648 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 648 54 54, g32p_row02_traceSegment_034_0648_0054, g32p_row02_traceSegment_034_0702_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0756_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 756 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0769_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 769 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0756_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 756 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 756 13 14, g32p_row02_traceSegment_034_0756_0013, g32p_row02_traceSegment_034_0769_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0783_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 783 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0796_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 796 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0783_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 783 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 783 13 14, g32p_row02_traceSegment_034_0783_0013, g32p_row02_traceSegment_034_0796_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0756_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 756 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 756 27 27, g32p_row02_traceSegment_034_0756_0027, g32p_row02_traceSegment_034_0783_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0810_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 810 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0823_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 823 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0810_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 810 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 810 13 14, g32p_row02_traceSegment_034_0810_0013, g32p_row02_traceSegment_034_0823_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0837_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 837 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0850_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 850 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0837_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 837 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 837 13 14, g32p_row02_traceSegment_034_0837_0013, g32p_row02_traceSegment_034_0850_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0810_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 810 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 810 27 27, g32p_row02_traceSegment_034_0810_0027, g32p_row02_traceSegment_034_0837_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0756_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 756 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 756 54 54, g32p_row02_traceSegment_034_0756_0054, g32p_row02_traceSegment_034_0810_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0648_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 648 216 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 648 108 108, g32p_row02_traceSegment_034_0648_0108, g32p_row02_traceSegment_034_0756_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0432_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 432 432 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 432 216 216, g32p_row02_traceSegment_034_0432_0216, g32p_row02_traceSegment_034_0648_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_0864 : g32p_coeffSegment g32p_row02_traceSegment_034 0 864 = [0, 0, 0, 0, 13] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 432 432, g32p_row02_traceSegment_034_0000_0432, g32p_row02_traceSegment_034_0432_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0864_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 864 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0877_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 877 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0864_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 864 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 864 13 14, g32p_row02_traceSegment_034_0864_0013, g32p_row02_traceSegment_034_0877_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0891_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 891 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0904_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 904 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0891_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 891 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 891 13 14, g32p_row02_traceSegment_034_0891_0013, g32p_row02_traceSegment_034_0904_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0864_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 864 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 864 27 27, g32p_row02_traceSegment_034_0864_0027, g32p_row02_traceSegment_034_0891_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0918_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 918 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0931_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 931 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0918_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 918 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 918 13 14, g32p_row02_traceSegment_034_0918_0013, g32p_row02_traceSegment_034_0931_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0945_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 945 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0958_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 958 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0945_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 945 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 945 13 14, g32p_row02_traceSegment_034_0945_0013, g32p_row02_traceSegment_034_0958_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0918_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 918 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 918 27 27, g32p_row02_traceSegment_034_0918_0027, g32p_row02_traceSegment_034_0945_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0864_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 864 108 = [0, 2, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 864 54 54, g32p_row02_traceSegment_034_0864_0054, g32p_row02_traceSegment_034_0918_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0972_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 972 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0985_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 985 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0972_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 972 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 972 13 14, g32p_row02_traceSegment_034_0972_0013, g32p_row02_traceSegment_034_0985_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0999_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 999 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1012_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1012 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_0999_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 999 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 999 13 14, g32p_row02_traceSegment_034_0999_0013, g32p_row02_traceSegment_034_1012_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0972_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 972 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 972 27 27, g32p_row02_traceSegment_034_0972_0027, g32p_row02_traceSegment_034_0999_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1026_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1026 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1039_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1039 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1026_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1026 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1026 13 14, g32p_row02_traceSegment_034_1026_0013, g32p_row02_traceSegment_034_1039_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1053_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1053 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1066_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1066 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1053_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1053 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1053 13 14, g32p_row02_traceSegment_034_1053_0013, g32p_row02_traceSegment_034_1066_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1026_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1026 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1026 27 27, g32p_row02_traceSegment_034_1026_0027, g32p_row02_traceSegment_034_1053_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0972_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 972 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 972 54 54, g32p_row02_traceSegment_034_0972_0054, g32p_row02_traceSegment_034_1026_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0864_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 864 216 = [0, 4, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 864 108 108, g32p_row02_traceSegment_034_0864_0108, g32p_row02_traceSegment_034_0972_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1080_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1080 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1093_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1093 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1080_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1080 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1080 13 14, g32p_row02_traceSegment_034_1080_0013, g32p_row02_traceSegment_034_1093_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1107_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1107 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1120_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1120 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1107_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1107 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1107 13 14, g32p_row02_traceSegment_034_1107_0013, g32p_row02_traceSegment_034_1120_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1080_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1080 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1080 27 27, g32p_row02_traceSegment_034_1080_0027, g32p_row02_traceSegment_034_1107_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1134_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1134 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1147_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1147 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1134_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1134 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1134 13 14, g32p_row02_traceSegment_034_1134_0013, g32p_row02_traceSegment_034_1147_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1161_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1161 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1174_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1174 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1161_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1161 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1161 13 14, g32p_row02_traceSegment_034_1161_0013, g32p_row02_traceSegment_034_1174_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1134_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1134 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1134 27 27, g32p_row02_traceSegment_034_1134_0027, g32p_row02_traceSegment_034_1161_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1080_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1080 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1080 54 54, g32p_row02_traceSegment_034_1080_0054, g32p_row02_traceSegment_034_1134_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1188_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1188 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1201_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1201 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1188_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1188 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1188 13 14, g32p_row02_traceSegment_034_1188_0013, g32p_row02_traceSegment_034_1201_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1215_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1215 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1228_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1228 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1215_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1215 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1215 13 14, g32p_row02_traceSegment_034_1215_0013, g32p_row02_traceSegment_034_1228_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1188_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1188 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1188 27 27, g32p_row02_traceSegment_034_1188_0027, g32p_row02_traceSegment_034_1215_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1242_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1242 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1255_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1255 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1242_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1242 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1242 13 14, g32p_row02_traceSegment_034_1242_0013, g32p_row02_traceSegment_034_1255_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1269_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1269 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1282_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1282 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1269_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1269 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1269 13 14, g32p_row02_traceSegment_034_1269_0013, g32p_row02_traceSegment_034_1282_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1242_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1242 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1242 27 27, g32p_row02_traceSegment_034_1242_0027, g32p_row02_traceSegment_034_1269_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1188_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1188 108 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1188 54 54, g32p_row02_traceSegment_034_1188_0054, g32p_row02_traceSegment_034_1242_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1080_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 1080 216 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1080 108 108, g32p_row02_traceSegment_034_1080_0108, g32p_row02_traceSegment_034_1188_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0864_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 864 432 = [0, 6, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 864 216 216, g32p_row02_traceSegment_034_0864_0216, g32p_row02_traceSegment_034_1080_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1296_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1296 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1309_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1309 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1296_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1296 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1296 13 14, g32p_row02_traceSegment_034_1296_0013, g32p_row02_traceSegment_034_1309_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1323_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1323 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1336_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1336 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1323_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1323 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1323 13 14, g32p_row02_traceSegment_034_1323_0013, g32p_row02_traceSegment_034_1336_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1296_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1296 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1296 27 27, g32p_row02_traceSegment_034_1296_0027, g32p_row02_traceSegment_034_1323_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1350_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1350 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1363_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1363 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1350_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1350 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1350 13 14, g32p_row02_traceSegment_034_1350_0013, g32p_row02_traceSegment_034_1363_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1377_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1377 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1390_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1390 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1377_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1377 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1377 13 14, g32p_row02_traceSegment_034_1377_0013, g32p_row02_traceSegment_034_1390_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1350_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1350 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1350 27 27, g32p_row02_traceSegment_034_1350_0027, g32p_row02_traceSegment_034_1377_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1296_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1296 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1296 54 54, g32p_row02_traceSegment_034_1296_0054, g32p_row02_traceSegment_034_1350_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1404_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1404 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1417_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1417 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1404_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1404 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1404 13 14, g32p_row02_traceSegment_034_1404_0013, g32p_row02_traceSegment_034_1417_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1431_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1431 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1444_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1444 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1431_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1431 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1431 13 14, g32p_row02_traceSegment_034_1431_0013, g32p_row02_traceSegment_034_1444_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1404_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1404 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1404 27 27, g32p_row02_traceSegment_034_1404_0027, g32p_row02_traceSegment_034_1431_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1458_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1458 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1471_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1471 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1458_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1458 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1458 13 14, g32p_row02_traceSegment_034_1458_0013, g32p_row02_traceSegment_034_1471_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1485_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1485 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1498_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1498 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1485_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1485 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1485 13 14, g32p_row02_traceSegment_034_1485_0013, g32p_row02_traceSegment_034_1498_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1458_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1458 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1458 27 27, g32p_row02_traceSegment_034_1458_0027, g32p_row02_traceSegment_034_1485_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1404_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1404 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1404 54 54, g32p_row02_traceSegment_034_1404_0054, g32p_row02_traceSegment_034_1458_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1296_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 1296 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1296 108 108, g32p_row02_traceSegment_034_1296_0108, g32p_row02_traceSegment_034_1404_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1512_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1512 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1525_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1525 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1512_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1512 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1512 13 14, g32p_row02_traceSegment_034_1512_0013, g32p_row02_traceSegment_034_1525_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1539_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1539 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1552_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1552 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1539_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1539 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1539 13 14, g32p_row02_traceSegment_034_1539_0013, g32p_row02_traceSegment_034_1552_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1512_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1512 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1512 27 27, g32p_row02_traceSegment_034_1512_0027, g32p_row02_traceSegment_034_1539_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1566_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1566 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1579_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1579 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1566_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1566 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1566 13 14, g32p_row02_traceSegment_034_1566_0013, g32p_row02_traceSegment_034_1579_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1593_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1593 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1606_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1606 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1593_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1593 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1593 13 14, g32p_row02_traceSegment_034_1593_0013, g32p_row02_traceSegment_034_1606_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1566_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1566 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1566 27 27, g32p_row02_traceSegment_034_1566_0027, g32p_row02_traceSegment_034_1593_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1512_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1512 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1512 54 54, g32p_row02_traceSegment_034_1512_0054, g32p_row02_traceSegment_034_1566_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1620_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1620 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1633_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1633 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1620_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1620 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1620 13 14, g32p_row02_traceSegment_034_1620_0013, g32p_row02_traceSegment_034_1633_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1647_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1647 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1660_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1660 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1647_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1647 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1647 13 14, g32p_row02_traceSegment_034_1647_0013, g32p_row02_traceSegment_034_1660_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1620_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1620 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1620 27 27, g32p_row02_traceSegment_034_1620_0027, g32p_row02_traceSegment_034_1647_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1674_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1674 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1687_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1687 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1674_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1674 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1674 13 14, g32p_row02_traceSegment_034_1674_0013, g32p_row02_traceSegment_034_1687_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1701_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1701 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1714_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1714 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1701_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1701 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1701 13 14, g32p_row02_traceSegment_034_1701_0013, g32p_row02_traceSegment_034_1714_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1674_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1674 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1674 27 27, g32p_row02_traceSegment_034_1674_0027, g32p_row02_traceSegment_034_1701_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1620_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1620 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1620 54 54, g32p_row02_traceSegment_034_1620_0054, g32p_row02_traceSegment_034_1674_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1512_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 1512 216 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1512 108 108, g32p_row02_traceSegment_034_1512_0108, g32p_row02_traceSegment_034_1620_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1296_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 1296 432 = [0, 2, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1296 216 216, g32p_row02_traceSegment_034_1296_0216, g32p_row02_traceSegment_034_1512_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0864_0864 : g32p_coeffSegment g32p_row02_traceSegment_034 864 864 = [0, 8, 0, 0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 864 432 432, g32p_row02_traceSegment_034_0864_0432, g32p_row02_traceSegment_034_1296_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_1728 : g32p_coeffSegment g32p_row02_traceSegment_034 0 1728 = [0, 8, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 864 864, g32p_row02_traceSegment_034_0000_0864, g32p_row02_traceSegment_034_0864_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1741_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1741 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1728 13 14, g32p_row02_traceSegment_034_1728_0013, g32p_row02_traceSegment_034_1741_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1755_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1755 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1768_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1768 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1755_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1755 27 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1755 13 14, g32p_row02_traceSegment_034_1755_0013, g32p_row02_traceSegment_034_1768_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1728 27 27, g32p_row02_traceSegment_034_1728_0027, g32p_row02_traceSegment_034_1755_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1782_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1782 13 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1795_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1795 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1782_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1782 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1782 13 14, g32p_row02_traceSegment_034_1782_0013, g32p_row02_traceSegment_034_1795_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1809_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1809 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1822_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1822 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1809_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1809 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1809 13 14, g32p_row02_traceSegment_034_1809_0013, g32p_row02_traceSegment_034_1822_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1782_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1782 54 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1782 27 27, g32p_row02_traceSegment_034_1782_0027, g32p_row02_traceSegment_034_1809_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 108 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1728 54 54, g32p_row02_traceSegment_034_1728_0054, g32p_row02_traceSegment_034_1782_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1836_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1836 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1849_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1849 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1836_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1836 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1836 13 14, g32p_row02_traceSegment_034_1836_0013, g32p_row02_traceSegment_034_1849_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1863_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1863 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1876_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1876 14 = [0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1863_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1863 27 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1863 13 14, g32p_row02_traceSegment_034_1863_0013, g32p_row02_traceSegment_034_1876_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1836_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1836 54 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1836 27 27, g32p_row02_traceSegment_034_1836_0027, g32p_row02_traceSegment_034_1863_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1890_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1890 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1903_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1903 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1890_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1890 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1890 13 14, g32p_row02_traceSegment_034_1890_0013, g32p_row02_traceSegment_034_1903_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1917_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1917 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1930_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1930 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1917_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1917 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1917 13 14, g32p_row02_traceSegment_034_1917_0013, g32p_row02_traceSegment_034_1930_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1890_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1890 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1890 27 27, g32p_row02_traceSegment_034_1890_0027, g32p_row02_traceSegment_034_1917_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1836_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1836 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1836 54 54, g32p_row02_traceSegment_034_1836_0054, g32p_row02_traceSegment_034_1890_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 216 = [0, 10] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1728 108 108, g32p_row02_traceSegment_034_1728_0108, g32p_row02_traceSegment_034_1836_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1944_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1944 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1957_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1957 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1944_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1944 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1944 13 14, g32p_row02_traceSegment_034_1944_0013, g32p_row02_traceSegment_034_1957_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1971_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1971 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1984_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 1984 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1971_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1971 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1971 13 14, g32p_row02_traceSegment_034_1971_0013, g32p_row02_traceSegment_034_1984_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1944_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1944 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1944 27 27, g32p_row02_traceSegment_034_1944_0027, g32p_row02_traceSegment_034_1971_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1998_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 1998 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2011_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2011 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_1998_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 1998 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1998 13 14, g32p_row02_traceSegment_034_1998_0013, g32p_row02_traceSegment_034_2011_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2025_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2025 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2038_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2038 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2025_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2025 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2025 13 14, g32p_row02_traceSegment_034_2025_0013, g32p_row02_traceSegment_034_2038_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1998_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 1998 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1998 27 27, g32p_row02_traceSegment_034_1998_0027, g32p_row02_traceSegment_034_2025_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1944_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 1944 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1944 54 54, g32p_row02_traceSegment_034_1944_0054, g32p_row02_traceSegment_034_1998_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2052_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2052 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2065_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2065 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2052_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2052 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2052 13 14, g32p_row02_traceSegment_034_2052_0013, g32p_row02_traceSegment_034_2065_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2079_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2079 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2092_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2092 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2079_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2079 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2079 13 14, g32p_row02_traceSegment_034_2079_0013, g32p_row02_traceSegment_034_2092_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2052_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2052 54 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2052 27 27, g32p_row02_traceSegment_034_2052_0027, g32p_row02_traceSegment_034_2079_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2106_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2106 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2119_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2119 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2106_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2106 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2106 13 14, g32p_row02_traceSegment_034_2106_0013, g32p_row02_traceSegment_034_2119_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2133_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2133 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2146_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2146 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2133_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2133 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2133 13 14, g32p_row02_traceSegment_034_2133_0013, g32p_row02_traceSegment_034_2146_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2106_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2106 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2106 27 27, g32p_row02_traceSegment_034_2106_0027, g32p_row02_traceSegment_034_2133_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2052_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2052 108 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2052 54 54, g32p_row02_traceSegment_034_2052_0054, g32p_row02_traceSegment_034_2106_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1944_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 1944 216 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1944 108 108, g32p_row02_traceSegment_034_1944_0108, g32p_row02_traceSegment_034_2052_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 432 = [0, 10, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1728 216 216, g32p_row02_traceSegment_034_1728_0216, g32p_row02_traceSegment_034_1944_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2160_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2160 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2173_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2173 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2160_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2160 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2160 13 14, g32p_row02_traceSegment_034_2160_0013, g32p_row02_traceSegment_034_2173_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2187_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2187 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2200_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2200 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2187_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2187 27 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2187 13 14, g32p_row02_traceSegment_034_2187_0013, g32p_row02_traceSegment_034_2200_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2160_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2160 54 = [0, 3] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2160 27 27, g32p_row02_traceSegment_034_2160_0027, g32p_row02_traceSegment_034_2187_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2214_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2214 13 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2227_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2227 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2214_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2214 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2214 13 14, g32p_row02_traceSegment_034_2214_0013, g32p_row02_traceSegment_034_2227_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2241_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2241 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2254_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2254 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2241_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2241 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2241 13 14, g32p_row02_traceSegment_034_2241_0013, g32p_row02_traceSegment_034_2254_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2214_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2214 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2214 27 27, g32p_row02_traceSegment_034_2214_0027, g32p_row02_traceSegment_034_2241_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2160_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2160 108 = [0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2160 54 54, g32p_row02_traceSegment_034_2160_0054, g32p_row02_traceSegment_034_2214_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2268_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2268 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2281_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2281 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2268_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2268 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2268 13 14, g32p_row02_traceSegment_034_2268_0013, g32p_row02_traceSegment_034_2281_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2295_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2295 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2308_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2308 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2295_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2295 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2295 13 14, g32p_row02_traceSegment_034_2295_0013, g32p_row02_traceSegment_034_2308_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2268_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2268 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2268 27 27, g32p_row02_traceSegment_034_2268_0027, g32p_row02_traceSegment_034_2295_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2322_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2322 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2335_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2335 14 = [0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2322_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2322 27 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2322 13 14, g32p_row02_traceSegment_034_2322_0013, g32p_row02_traceSegment_034_2335_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2349_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2349 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2362_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2362 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2349_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2349 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2349 13 14, g32p_row02_traceSegment_034_2349_0013, g32p_row02_traceSegment_034_2362_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2322_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2322 54 = [0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2322 27 27, g32p_row02_traceSegment_034_2322_0027, g32p_row02_traceSegment_034_2349_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2268_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2268 108 = [0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2268 54 54, g32p_row02_traceSegment_034_2268_0054, g32p_row02_traceSegment_034_2322_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2160_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 2160 216 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2160 108 108, g32p_row02_traceSegment_034_2160_0108, g32p_row02_traceSegment_034_2268_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2376_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2376 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2389_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2389 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2376_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2376 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2376 13 14, g32p_row02_traceSegment_034_2376_0013, g32p_row02_traceSegment_034_2389_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2403_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2403 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2416_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2416 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2403_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2403 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2403 13 14, g32p_row02_traceSegment_034_2403_0013, g32p_row02_traceSegment_034_2416_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2376_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2376 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2376 27 27, g32p_row02_traceSegment_034_2376_0027, g32p_row02_traceSegment_034_2403_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2430_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2430 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2443_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2443 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2430_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2430 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2430 13 14, g32p_row02_traceSegment_034_2430_0013, g32p_row02_traceSegment_034_2443_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2457_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2457 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2470_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2470 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2457_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2457 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2457 13 14, g32p_row02_traceSegment_034_2457_0013, g32p_row02_traceSegment_034_2470_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2430_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2430 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2430 27 27, g32p_row02_traceSegment_034_2430_0027, g32p_row02_traceSegment_034_2457_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2376_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2376 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2376 54 54, g32p_row02_traceSegment_034_2376_0054, g32p_row02_traceSegment_034_2430_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2484_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2484 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2497_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2497 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2484_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2484 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2484 13 14, g32p_row02_traceSegment_034_2484_0013, g32p_row02_traceSegment_034_2497_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2511_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2511 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2524_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2524 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2511_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2511 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2511 13 14, g32p_row02_traceSegment_034_2511_0013, g32p_row02_traceSegment_034_2524_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2484_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2484 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2484 27 27, g32p_row02_traceSegment_034_2484_0027, g32p_row02_traceSegment_034_2511_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2538_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2538 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2551_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2551 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2538_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2538 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2538 13 14, g32p_row02_traceSegment_034_2538_0013, g32p_row02_traceSegment_034_2551_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2565_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2565 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2578_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2578 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2565_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2565 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2565 13 14, g32p_row02_traceSegment_034_2565_0013, g32p_row02_traceSegment_034_2578_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2538_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2538 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2538 27 27, g32p_row02_traceSegment_034_2538_0027, g32p_row02_traceSegment_034_2565_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2484_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2484 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2484 54 54, g32p_row02_traceSegment_034_2484_0054, g32p_row02_traceSegment_034_2538_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2376_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 2376 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2376 108 108, g32p_row02_traceSegment_034_2376_0108, g32p_row02_traceSegment_034_2484_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2160_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 2160 432 = [0, 6] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2160 216 216, g32p_row02_traceSegment_034_2160_0216, g32p_row02_traceSegment_034_2376_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_0864 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 864 = [0, 16, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1728 432 432, g32p_row02_traceSegment_034_1728_0432, g32p_row02_traceSegment_034_2160_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2592_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2592 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2605_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2605 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2592_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2592 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2592 13 14, g32p_row02_traceSegment_034_2592_0013, g32p_row02_traceSegment_034_2605_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2619_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2619 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2632_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2632 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2619_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2619 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2619 13 14, g32p_row02_traceSegment_034_2619_0013, g32p_row02_traceSegment_034_2632_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2592_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2592 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2592 27 27, g32p_row02_traceSegment_034_2592_0027, g32p_row02_traceSegment_034_2619_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2646_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2646 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2659_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2659 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2646_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2646 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2646 13 14, g32p_row02_traceSegment_034_2646_0013, g32p_row02_traceSegment_034_2659_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2673_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2673 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2686_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2686 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2673_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2673 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2673 13 14, g32p_row02_traceSegment_034_2673_0013, g32p_row02_traceSegment_034_2686_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2646_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2646 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2646 27 27, g32p_row02_traceSegment_034_2646_0027, g32p_row02_traceSegment_034_2673_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2592_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2592 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2592 54 54, g32p_row02_traceSegment_034_2592_0054, g32p_row02_traceSegment_034_2646_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2700_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2700 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2713_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2713 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2700_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2700 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2700 13 14, g32p_row02_traceSegment_034_2700_0013, g32p_row02_traceSegment_034_2713_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2727_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2727 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2740_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2740 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2727_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2727 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2727 13 14, g32p_row02_traceSegment_034_2727_0013, g32p_row02_traceSegment_034_2740_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2700_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2700 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2700 27 27, g32p_row02_traceSegment_034_2700_0027, g32p_row02_traceSegment_034_2727_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2754_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2754 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2767_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2767 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2754_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2754 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2754 13 14, g32p_row02_traceSegment_034_2754_0013, g32p_row02_traceSegment_034_2767_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2781_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2781 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2794_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2794 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2781_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2781 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2781 13 14, g32p_row02_traceSegment_034_2781_0013, g32p_row02_traceSegment_034_2794_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2754_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2754 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2754 27 27, g32p_row02_traceSegment_034_2754_0027, g32p_row02_traceSegment_034_2781_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2700_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2700 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2700 54 54, g32p_row02_traceSegment_034_2700_0054, g32p_row02_traceSegment_034_2754_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2592_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 2592 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2592 108 108, g32p_row02_traceSegment_034_2592_0108, g32p_row02_traceSegment_034_2700_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2808_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2808 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2821_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2821 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2808_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2808 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2808 13 14, g32p_row02_traceSegment_034_2808_0013, g32p_row02_traceSegment_034_2821_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2835_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2835 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2848_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2848 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2835_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2835 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2835 13 14, g32p_row02_traceSegment_034_2835_0013, g32p_row02_traceSegment_034_2848_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2808_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2808 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2808 27 27, g32p_row02_traceSegment_034_2808_0027, g32p_row02_traceSegment_034_2835_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2862_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2862 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2875_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2875 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2862_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2862 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2862 13 14, g32p_row02_traceSegment_034_2862_0013, g32p_row02_traceSegment_034_2875_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2889_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2889 13 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2902_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2902 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2889_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2889 27 = [0, 0, 0, 0, 4] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2889 13 14, g32p_row02_traceSegment_034_2889_0013, g32p_row02_traceSegment_034_2902_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2862_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2862 54 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2862 27 27, g32p_row02_traceSegment_034_2862_0027, g32p_row02_traceSegment_034_2889_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2808_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2808 108 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2808 54 54, g32p_row02_traceSegment_034_2808_0054, g32p_row02_traceSegment_034_2862_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2916_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2916 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2929_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2929 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2916_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2916 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2916 13 14, g32p_row02_traceSegment_034_2916_0013, g32p_row02_traceSegment_034_2929_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2943_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2943 13 = [0, 0, 0, 0, 3] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2956_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2956 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2943_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2943 27 = [0, 0, 0, 0, 5] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2943 13 14, g32p_row02_traceSegment_034_2943_0013, g32p_row02_traceSegment_034_2956_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2916_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2916 54 = [0, 0, 0, 0, 7] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2916 27 27, g32p_row02_traceSegment_034_2916_0027, g32p_row02_traceSegment_034_2943_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2970_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2970 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2983_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 2983 14 = [0, 0, 0, 0, 2] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2970_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2970 27 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2970 13 14, g32p_row02_traceSegment_034_2970_0013, g32p_row02_traceSegment_034_2983_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2997_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 2997 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3010_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3010 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_2997_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 2997 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2997 13 14, g32p_row02_traceSegment_034_2997_0013, g32p_row02_traceSegment_034_3010_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2970_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 2970 54 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2970 27 27, g32p_row02_traceSegment_034_2970_0027, g32p_row02_traceSegment_034_2997_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2916_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 2916 108 = [0, 0, 0, 0, 9] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2916 54 54, g32p_row02_traceSegment_034_2916_0054, g32p_row02_traceSegment_034_2970_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2808_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 2808 216 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2808 108 108, g32p_row02_traceSegment_034_2808_0108, g32p_row02_traceSegment_034_2916_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2592_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 2592 432 = [0, 0, 0, 0, 14] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2592 216 216, g32p_row02_traceSegment_034_2592_0216, g32p_row02_traceSegment_034_2808_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3024_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3024 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3037_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3037 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3024_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3024 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3024 13 14, g32p_row02_traceSegment_034_3024_0013, g32p_row02_traceSegment_034_3037_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3051_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3051 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3064_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3064 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3051_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3051 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3051 13 14, g32p_row02_traceSegment_034_3051_0013, g32p_row02_traceSegment_034_3064_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3024_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3024 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3024 27 27, g32p_row02_traceSegment_034_3024_0027, g32p_row02_traceSegment_034_3051_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3078_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3078 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3091_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3091 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3078_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3078 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3078 13 14, g32p_row02_traceSegment_034_3078_0013, g32p_row02_traceSegment_034_3091_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3105_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3105 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3118_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3118 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3105_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3105 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3105 13 14, g32p_row02_traceSegment_034_3105_0013, g32p_row02_traceSegment_034_3118_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3078_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3078 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3078 27 27, g32p_row02_traceSegment_034_3078_0027, g32p_row02_traceSegment_034_3105_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3024_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 3024 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3024 54 54, g32p_row02_traceSegment_034_3024_0054, g32p_row02_traceSegment_034_3078_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3132_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3132 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3145_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3145 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3132_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3132 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3132 13 14, g32p_row02_traceSegment_034_3132_0013, g32p_row02_traceSegment_034_3145_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3159_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3159 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3172_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3172 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3159_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3159 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3159 13 14, g32p_row02_traceSegment_034_3159_0013, g32p_row02_traceSegment_034_3172_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3132_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3132 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3132 27 27, g32p_row02_traceSegment_034_3132_0027, g32p_row02_traceSegment_034_3159_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3186_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3186 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3199_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3199 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3186_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3186 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3186 13 14, g32p_row02_traceSegment_034_3186_0013, g32p_row02_traceSegment_034_3199_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3213_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3213 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3226_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3226 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3213_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3213 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3213 13 14, g32p_row02_traceSegment_034_3213_0013, g32p_row02_traceSegment_034_3226_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3186_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3186 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3186 27 27, g32p_row02_traceSegment_034_3186_0027, g32p_row02_traceSegment_034_3213_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3132_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 3132 108 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3132 54 54, g32p_row02_traceSegment_034_3132_0054, g32p_row02_traceSegment_034_3186_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3024_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 3024 216 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3024 108 108, g32p_row02_traceSegment_034_3024_0108, g32p_row02_traceSegment_034_3132_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3240_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3240 13 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3253_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3253 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3240_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3240 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3240 13 14, g32p_row02_traceSegment_034_3240_0013, g32p_row02_traceSegment_034_3253_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3267_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3267 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3280_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3280 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3267_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3267 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3267 13 14, g32p_row02_traceSegment_034_3267_0013, g32p_row02_traceSegment_034_3280_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3240_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3240 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3240 27 27, g32p_row02_traceSegment_034_3240_0027, g32p_row02_traceSegment_034_3267_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3294_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3294 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3307_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3307 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3294_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3294 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3294 13 14, g32p_row02_traceSegment_034_3294_0013, g32p_row02_traceSegment_034_3307_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3321_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3321 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3334_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3334 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3321_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3321 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3321 13 14, g32p_row02_traceSegment_034_3321_0013, g32p_row02_traceSegment_034_3334_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3294_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3294 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3294 27 27, g32p_row02_traceSegment_034_3294_0027, g32p_row02_traceSegment_034_3321_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3240_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 3240 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3240 54 54, g32p_row02_traceSegment_034_3240_0054, g32p_row02_traceSegment_034_3294_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3348_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3348 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3361_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3361 14 = [0, 0, 0, 0, 1] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3348_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3348 27 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3348 13 14, g32p_row02_traceSegment_034_3348_0013, g32p_row02_traceSegment_034_3361_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3375_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3375 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3388_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3388 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3375_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3375 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3375 13 14, g32p_row02_traceSegment_034_3375_0013, g32p_row02_traceSegment_034_3388_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3348_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3348 54 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3348 27 27, g32p_row02_traceSegment_034_3348_0027, g32p_row02_traceSegment_034_3375_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3402_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3402 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3415_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3415 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3402_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3402 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3402 13 14, g32p_row02_traceSegment_034_3402_0013, g32p_row02_traceSegment_034_3415_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3429_0013 : g32p_coeffSegment g32p_row02_traceSegment_034 3429 13 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3442_0014 : g32p_coeffSegment g32p_row02_traceSegment_034 3442 14 = [] := by
  decide +kernel

private theorem g32p_row02_traceSegment_034_3429_0027 : g32p_coeffSegment g32p_row02_traceSegment_034 3429 27 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3429 13 14, g32p_row02_traceSegment_034_3429_0013, g32p_row02_traceSegment_034_3442_0014]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3402_0054 : g32p_coeffSegment g32p_row02_traceSegment_034 3402 54 = [] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3402 27 27, g32p_row02_traceSegment_034_3402_0027, g32p_row02_traceSegment_034_3429_0027]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3348_0108 : g32p_coeffSegment g32p_row02_traceSegment_034 3348 108 = [0, 0, 0, 0, 1] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3348 54 54, g32p_row02_traceSegment_034_3348_0054, g32p_row02_traceSegment_034_3402_0054]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3240_0216 : g32p_coeffSegment g32p_row02_traceSegment_034 3240 216 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3240 108 108, g32p_row02_traceSegment_034_3240_0108, g32p_row02_traceSegment_034_3348_0108]
  decide +kernel

private theorem g32p_row02_traceSegment_034_3024_0432 : g32p_coeffSegment g32p_row02_traceSegment_034 3024 432 = [0, 0, 0, 0, 2] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 3024 216 216, g32p_row02_traceSegment_034_3024_0216, g32p_row02_traceSegment_034_3240_0216]
  decide +kernel

private theorem g32p_row02_traceSegment_034_2592_0864 : g32p_coeffSegment g32p_row02_traceSegment_034 2592 864 = [0, 0, 0, 0, 16] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 2592 432 432, g32p_row02_traceSegment_034_2592_0432, g32p_row02_traceSegment_034_3024_0432]
  decide +kernel

private theorem g32p_row02_traceSegment_034_1728_1728 : g32p_coeffSegment g32p_row02_traceSegment_034 1728 1728 = [0, 16, 0, 0, 20] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 1728 864 864, g32p_row02_traceSegment_034_1728_0864, g32p_row02_traceSegment_034_2592_0864]
  decide +kernel

private theorem g32p_row02_traceSegment_034_0000_3456 : g32p_coeffSegment g32p_row02_traceSegment_034 0 3456 = [0, 24, 0, 0, 36] := by
  rw [g32p_coeffSegment_add g32p_row02_traceSegment_034 0 1728 1728, g32p_row02_traceSegment_034_0000_1728, g32p_row02_traceSegment_034_1728_1728]
  decide +kernel

theorem g32p_row02_traceCoefficients_034 :
    g32p_supplierTraceCoefficients g32p_row02_supplierClassifier
      (fun j => (Multiplicative.toAdd (g32p_row02_characterValues j)).val) 34 = [0, 24, 0, 0, 36] := by
  rw [g32p_supplierTraceCoefficients_segment]
  exact g32p_row02_traceSegment_034_0000_3456

end HodgeLean.Foundations.Program

end
end
